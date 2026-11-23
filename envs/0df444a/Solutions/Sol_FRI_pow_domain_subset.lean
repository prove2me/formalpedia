-- Prove2me | solution 1 for FRI_pow_domain_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:40:25.177971+00:00
-- url     : https://prove2.me/submissions/8a990802-9a04-4b16-a8c0-cd8671cf63a6

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
import Theorems.Thm_FRI_domain_step_prop

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (i : ℕ) (h : i < P.num_foldings)
    (S : Finset F) (hS : S ⊆ FRI_domain P i) :
    pow_domain S (P.m ⟨i, h⟩) ⊆ FRI_domain P (i + 1) :=
  Finset.image_subset_iff.mpr fun x hx => FRI_domain_step_prop P i h x (hS hx)
