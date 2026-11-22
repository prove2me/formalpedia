-- Prove2me | solution 1 for BooleanIsoperimetry.slice1_eq_filter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:26.615024+00:00
-- url     : https://prove2.me/submissions/c5eb4123-b0dc-461f-8926-f3234cde5a21

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_rank_embed1
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k : ℕ} :
    slice1 (simplicialInitSeg (n + 1) k)
      = Finset.univ.filter
          (fun w : Cube n => rank w + binomPrefix n (w.card + 1) < k) := by
  ext w
  simp only [slice1, Finset.mem_filter, Finset.mem_univ, true_and, simplicialInitSeg,
    rank_embed1]
end BooleanIsoperimetry
