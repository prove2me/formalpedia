-- Prove2me | solution 1 for DenseTriangleFree.list_sum_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:35.656709+00:00
-- url     : https://prove2.me/submissions/4a77c99f-531e-42f1-a580-eb7ea8a6135b

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Heavy

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
namespace DenseTriangleFree
theorem _root_.solution (ws : List ℕ) : ws.sum = ∑ i ∈ Finset.range ws.length, ws.getD i 0 := by
  induction ws with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons, ih]; simp [add_comm]
end DenseTriangleFree
