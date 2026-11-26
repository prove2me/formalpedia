-- Prove2me | solution 1 for DenseTriangleFree.wsumL_filter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:56.181847+00:00
-- url     : https://prove2.me/submissions/8648ef62-6189-4da9-bd1e-d443bf4260c0

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Heavy
public import Theorems.Thm_DenseTriangleFree_listsum_range
public import Theorems.Thm_P2M_DenseTriangleFree_sum_map_filter__6198be9b6b06

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
namespace DenseTriangleFree
theorem _root_.solution (ws : List ℕ) (q : ℕ → Prop) [DecidablePred q] :
    wsumL ws (((List.range ws.length).filter fun i => 0 < ws.getD i 0).filter
      (fun i => decide (q i))) =
      ∑ i ∈ Finset.range ws.length, (if q i then ws.getD i 0 else 0) := by
  unfold wsumL
  rw [sum_map_filter', ← listsum_range]
  have := sum_map_filter' (p := fun i => 0 < ws.getD i 0) (List.range ws.length)
    (fun i => if q i then ws.getD i 0 else 0)
  rw [this]
  congr 1
  apply List.map_congr_left
  intro i _
  split_ifs <;> omega
end DenseTriangleFree
