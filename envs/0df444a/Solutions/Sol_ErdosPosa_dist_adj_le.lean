-- Prove2me | solution 1 for ErdosPosa.dist_adj_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:22:29.175628+00:00
-- url     : https://prove2.me/submissions/453dec79-63c9-4f34-bf98-eba63a12c933

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Definitions.Def_ErdosPosaLib_EPMoore

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*} {H : SimpleGraph V}
namespace ErdosPosa
theorem _root_.solution {v x y : V} (hx : H.Reachable v x) (hxy : H.Adj x y) :
    H.dist v y ≤ H.dist v x + 1 := by
  obtain ⟨q, hq⟩ := hx.exists_walk_length_eq_dist
  calc H.dist v y ≤ (q.concat hxy).length := dist_le _
    _ = _ := by rw [Walk.length_concat, hq]
end ErdosPosa
