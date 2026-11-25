-- Prove2me | solution 1 for Complex.sum_mul_pow_isBigO_pow_iff_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:29:39.130241+00:00
-- url     : https://prove2.me/submissions/ba2b49bf-c175-4f9a-b7bb-afa510989e06

import Mathlib
import Definitions.Def_RPLib_S3_ExpSum

set_option autoImplicit false

theorem solution (s : Finset ℂ) (c : ℂ → ℂ) (R : ℝ) (hR : 0 ≤ R) :
    Asymptotics.IsBigO Filter.atTop (fun m : ℕ => ∑ z ∈ s, c z * z ^ m) (fun m : ℕ => R ^ m) ↔
      ∀ z ∈ s, c z ≠ 0 → ‖z‖ ≤ R := by
  exact RamanujanPetersson.ExpSum.expSum_isBigO_iff s c hR
