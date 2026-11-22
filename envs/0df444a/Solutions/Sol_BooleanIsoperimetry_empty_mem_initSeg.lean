-- Prove2me | solution 1 for BooleanIsoperimetry.empty_mem_initSeg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:48.714804+00:00
-- url     : https://prove2.me/submissions/d36b3d82-ca38-4488-a736-16e242a45404

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_zero
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ
public import Theorems.Thm_BooleanIsoperimetry_rank_lt_binomPrefix_iff
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k : ℕ} (hk : 1 ≤ k) :
    (∅ : Cube n) ∈ simplicialInitSeg n k := by
  simp only [simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and]
  have hb : binomPrefix n 1 = 1 := by simp [binomPrefix_succ, binomPrefix_zero]
  have hr : rank (∅ : Cube n) < 1 := by
    have h := (rank_lt_binomPrefix_iff (n := n) (c := 1) (∅ : Cube n)).mpr (by simp)
    rwa [hb] at h
  omega
end BooleanIsoperimetry
