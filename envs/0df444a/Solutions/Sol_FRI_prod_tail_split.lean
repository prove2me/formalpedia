-- Prove2me | solution 1 for FRI_prod_tail_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:01:35.323342+00:00
-- url     : https://prove2.me/submissions/8014fad9-2385-46e3-86e7-1a0adf847184

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (i : ℕ) (hi : i < P.num_foldings) :
    FRI_prod_tail P i = P.m ⟨i, hi⟩ * FRI_prod_tail P (i + 1) := by
  simp only [FRI_prod_tail]
  have h_mem : (⟨i, hi⟩ : Fin P.num_foldings) ∈
      Finset.univ.filter (fun j : Fin P.num_foldings ↦ i ≤ (j : ℕ)) := by grind
  rw [← Finset.mul_prod_erase _ _ h_mem]
  congr 1
  apply Finset.prod_congr
  · ext j
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_ne_iff.symm]
    omega
  · intro _ _; rfl
