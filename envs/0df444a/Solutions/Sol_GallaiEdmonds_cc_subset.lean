-- Prove2me | solution 1 for GallaiEdmonds.cc_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:57:15.850096+00:00
-- url     : https://prove2.me/submissions/81b9aedc-ac86-4ec5-a4fe-b92edbb6b940

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution : cc G W x ⊆ W := fun _ ⟨_, hy, _⟩ => hy
end GallaiEdmonds
