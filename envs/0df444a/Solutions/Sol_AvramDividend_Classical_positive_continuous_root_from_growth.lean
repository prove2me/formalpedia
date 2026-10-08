-- Prove2me | solution 1 for AvramDividend.Classical.positive_continuous_root_from_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:59:56.179024+00:00
-- url     : https://prove2.me/submissions/ecb4718f-7919-4193-a25d-f0f1d8a253de

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Set

/-- A continuous positive-level crossing from zero produces a positive root. -/
theorem solution
    (f : ℝ → ℝ) (q A : ℝ) (hq : 0 < q) (hA : 0 < A)
    (hcont : ContinuousOn f (Ici (0 : ℝ)))
    (h0 : f 0 = 0) (hgt : q < f A) :
    ∃ φ : ℝ, 0 < φ ∧ φ ≤ A ∧ f φ = q := by
  have hcontI : ContinuousOn f (Icc (0 : ℝ) A) :=
    hcont.mono (by
      intro x hx
      exact hx.1)
  have hqmem : q ∈ Icc (f 0) (f A) := by
    constructor
    · rw [h0]
      exact le_of_lt hq
    · exact le_of_lt hgt
  obtain ⟨φ, hφI, hφeq⟩ :=
    intermediate_value_Icc (le_of_lt hA) hcontI hqmem
  have hφpos : 0 < φ := by
    rcases hφI with ⟨hφnonneg, hφle⟩
    exact lt_of_le_of_ne hφnonneg (by
      intro hzero
      have hh : φ = 0 := hzero.symm
      rw [hh, h0] at hφeq
      exact (ne_of_gt hq) hφeq.symm)
  exact ⟨φ, hφpos, hφI.2, hφeq⟩
