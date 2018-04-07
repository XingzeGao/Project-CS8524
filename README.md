# Project-CS8524
Xingze Gao, Weilian Fu

Verify the feasibility of implement multimap in Dafny.

## updates on 4/6
In order to understand the way to implement map in Dafny, we first analyse the source code in Dafny to implement a set. As we all know that set is a container used to store a bunch of values and the data in set shouldn't be the same. Multiset is almost the same as set, but it doesn't need the value stored in multiset to be unique. Map and multimap have the same potential theory as set and multiset, instead to store single data, they are used to store key-value pairs. And we can use the key to search corresponding values. The source code shows that unlike Java or C++ the set in Dafny is based on the normal binary search tree. 
```
  ghost var Repr: set<object>;
  ghost var elems: set<int>;

  var data: int;
  var left: SetNode;
  var right: SetNode;
```
This is the data structure in Dafny to store values for set. Each node has a varable "data" used to store the value and two SetNode variable used to point to the left and right subtrees.
```
   method Double(p: int, q: int)
    modifies this;
//    requires p != q;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {p, q};
  {
    if (q > p) {
      var gensym79 := new SetNode;
      gensym79.Init(q);
      this.data := p;
      this.elems := {p, q};
      this.left := null;
      this.right := gensym79;
      this.Repr := {this} + this.right.Repr;
    } else if (q < p) {
      var gensym79 := new SetNode;
      gensym79.Init(p);
      this.data := q;
      this.elems := {p, q};
      this.left := null;
      this.right := gensym79;
      this.Repr := {this} + this.right.Repr;
    } else {
      this.data := p; 
      this.elems := {p};
      this.left := null;
      this.right := null;
      this.Repr := {this};
    } 
  }

  method Triple(p: int, q: int, r: int)
    modifies this;
    requires p != q;
    requires q != r;
    requires r != p;
    ensures fresh(Repr - {this});
    ensures Valid();
    ensures elems == {p, q, r};
  {
    if (p < q && r > q) {
      var gensym83 := new SetNode;
      var gensym84 := new SetNode;
      gensym83.Init(r);
      gensym84.Init(p);
      this.data := q;
      this.elems := {p, q, r};
      this.left := gensym84;
      this.right := gensym83;
      this.Repr := ({this} + this.left.Repr) + this.right.Repr;
    } else {
      if (p < r && q > r) {
        var gensym85 := new SetNode;
        var gensym86 := new SetNode;
        gensym85.Init(q);
        gensym86.Init(p);
        this.data := r;
        this.elems := {p, q, r};
        this.left := gensym86;
        this.right := gensym85;
        this.Repr := ({this} + this.left.Repr) + this.right.Repr;
      } else {
        if (r < p && q > p) {
          var gensym84 := new SetNode;
          var gensym85 := new SetNode;
          gensym84.Init(q);
          gensym85.Init(r);
          this.data := p;
          this.elems := {p, q, r};
          this.left := gensym85;
          this.right := gensym84;
          this.Repr := ({this} + this.left.Repr) + this.right.Repr;
        } else {
          if (q < p && r > p) {
            var gensym82 := new SetNode;
            var gensym83 := new SetNode;
            gensym82.Init(r);
            gensym83.Init(q);
            this.data := p;
            this.elems := {p, q, r};
            this.left := gensym83;
            this.right := gensym82;
            this.Repr := ({this} + this.left.Repr) + this.right.Repr;
          } else {
            if (q < r && p > r) {
              var gensym85 := new SetNode;
              var gensym86 := new SetNode;
              gensym85.Init(p);
              gensym86.Init(q);
              this.data := r;
              this.elems := {p, q, r};
              this.left := gensym86;
              this.right := gensym85;
              this.Repr := ({this} + this.left.Repr) + this.right.Repr;
            } else {
              var gensym82 := new SetNode;
              var gensym83 := new SetNode;
              gensym82.Init(p);
              gensym83.Init(r);
              this.data := q;
              this.elems := {p, q, r};
              this.left := gensym83;
              this.right := gensym82;
              this.Repr := ({this} + this.left.Repr) + this.right.Repr;
            }
          }
        }
      }
    }
  }
  ```
  
  To insert values into a set, Dafny provide two different interfaces to users. These two method have two and three parameters respectively. For each insertion, the stored value always recursive follow the rules that the value of node always greater than values stored in its left subtree and smaller than values stored in its right subtree.
  
  
##References:
https://github.com/Microsoft/dafny/blob/171ef037493eed6a90423c6497c8ba88de077de9/Source/Jennisys/examples/set.dfy 
https://github.com/Microsoft/dafny/blob/171ef037493eed6a90423c6497c8ba88de077de9/Source/Dafny/Compiler.cs
https://github.com/Microsoft/dafny/blob/171ef037493eed6a90423c6497c8ba88de077de9/Binaries/DafnyRuntime.cs 

