-- Prove2me | solution 1 for BooleanIsoperimetry.rank_lt_binomPrefix_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:03.041795+00:00
-- url     : https://prove2.me/submissions/9c4a5ffa-993f-41f6-8253-3a0b1c1252b1

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_lowCard_eq_initSeg
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n c : ℕ} (w : Cube n) :
    rank w < binomPrefix n c ↔ w.card < c := by
  have h := lowCard_eq_initSeg n c
  have hmem : w ∈ Finset.univ.filter (fun w : Cube n => w.card < c)
      ↔ w ∈ simplicialInitSeg n (binomPrefix n c) := by rw [h]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, simplicialInitSeg] at hmem
  exact hmem.symm
end BooleanIsoperimetry
