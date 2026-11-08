-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps13_zero_extension_upper_contact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T15:36:02.996399+00:00
-- url     : https://prove2.me/submissions/a0f83d69-7dc1-4e65-8dca-551f2fb70ed0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

/-! The zero extension has a one-sided upper envelope even if `w 0 > 0`. -/
theorem solution
    (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ, |y| < δ → w y ≤ w 0 + ε := by
  intro ε hε
  have hc : ContinuousWithinAt w (Ici (0 : ℝ)) 0 :=
    hwcont 0 (by simp)
  obtain ⟨δ, hδ, hnear⟩ :=
    (Metric.continuousWithinAt_iff.mp hc) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  by_cases hnonneg : 0 ≤ y
  · have hmem : y ∈ Ici (0 : ℝ) := by simpa using hnonneg
    have hdist : dist y (0 : ℝ) < δ := by
      simpa [Real.dist_eq] using hy
    have hwclose : dist (w y) (w 0) < ε := hnear hmem hdist
    have hdiff : |w y - w 0| < ε := by
      simpa [Real.dist_eq] using hwclose
    linarith [(abs_lt.mp hdiff).2]
  · have hyneg : y < 0 := lt_of_not_ge hnonneg
    rw [hwneg y hyneg]
    linarith
