-- Prove2me | solution 1 for FRI_domain_foldable_strong
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:30:16.608797+00:00
-- url     : https://prove2.me/submissions/c4931b01-f99a-4f1c-9c27-4085db7aa7ae

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
import Theorems.Thm_FRI_prod_tail_zero
import Theorems.Thm_FRI_prod_tail_split
import Theorems.Thm_IsFoldable_pow_domain

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (i : ℕ) (hi : i ≤ P.num_foldings) :
    IsFoldable (FRI_domain P i) (FRI_prod_tail P i) := by
  induction i with
  | zero => simpa [FRI_domain, FRI_prod_tail_zero] using P.h_D0_foldable
  | succ i ih =>
    by_cases h : i < P.num_foldings
    · specialize ih h.le
      simp only [FRI_domain, h, ↓reduceDIte]
      rw [FRI_prod_tail_split P i h] at ih
      exact IsFoldable_pow_domain ih (P.h_m_pos ⟨i, h⟩)
    · grind
