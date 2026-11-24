-- Prove2me | solution 2 for FockRaiseLowGrade.hc_hc
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T04:36:49.416843+00:00
-- url     : https://prove2.me/submissions/ac0bfb4c-ddbc-4d66-9d90-5c12f39b6334

import Mathlib
open MvPolynomial
variable {σ : Type*}


theorem solution (m n : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent m (homogeneousComponent n P) =
      if m = n then homogeneousComponent n P else 0 := by
  classical
  by_cases h : m = n
  · subst m; ext d; by_cases hd : Finsupp.degree d = n <;> simp [coeff_homogeneousComponent,hd]
  · rw [if_neg h]; ext d; simp only [coeff_homogeneousComponent,coeff_zero]; split_ifs <;> first | rfl | omega
