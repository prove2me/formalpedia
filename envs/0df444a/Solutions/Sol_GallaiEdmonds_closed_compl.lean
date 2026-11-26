-- Prove2me | solution 1 for GallaiEdmonds.closed_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:59:58.743716+00:00
-- url     : https://prove2.me/submissions/91325b20-40e2-46bd-83b2-58aad161e188

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
theorem _root_.solution (hc : Closed G W W') : Closed G W (W \ W') := by
  intro y hy z hz hadj
  exact ⟨hz, fun hz' => hy.2 (hc z hz' y hy.1 hadj.symm)⟩
end GallaiEdmonds
