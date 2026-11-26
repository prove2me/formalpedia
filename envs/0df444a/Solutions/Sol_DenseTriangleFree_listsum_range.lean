-- Prove2me | solution 1 for DenseTriangleFree.listsum_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:31.307479+00:00
-- url     : https://prove2.me/submissions/59c4ef7b-5028-4fad-96a4-eda301967140

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
theorem _root_.solution (n : ℕ) (g : ℕ → ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp
end DenseTriangleFree
