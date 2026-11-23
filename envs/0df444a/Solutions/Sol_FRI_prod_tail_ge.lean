-- Prove2me | solution 1 for FRI_prod_tail_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:40:19.86996+00:00
-- url     : https://prove2.me/submissions/18d4f8f4-6d4f-4d15-ba22-ed81e7c6f799

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F)
    (i : ℕ) (hi : P.num_foldings ≤ i) :
    FRI_prod_tail P i = 1 := by
  simp only [FRI_prod_tail]
  rw [Finset.filter_eq_empty_iff.mpr, Finset.prod_empty]
  intro j _
  grind
