-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f7_hjb_topcap_global_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:28:47.574057+00:00
-- url     : https://prove2.me/submissions/88daac47-a287-468a-aa7f-c4ff4a1bf7f6

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_positive_deriv_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal

/-- A top-cap C² HJB supersolution has nonnegative value everywhere:
positive-reserve monotonicity extends across zero; negative reserves vanish. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤) :
    ∀ y : ℝ, 0 ≤ w y := by
  have hS : {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} = Ioi (0 : ℝ) := by
    ext y
    simp [hTop]
  have hd : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ w y := by
    intro y hy
    have hmem : y ∈ {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} := by
      simp [hy, hTop]
    exact (hw_smooth.contDiffAt
      (by simpa [hS] using (isOpen_Ioi.mem_nhds hy))).differentiableAt (by norm_num)
  have hg : ∀ y : ℝ, 0 < y → 1 ≤ deriv w y := by
    intro y hy
    exact hw_grad y hy (by simp [hTop])
  have hnonneg :=
    (AvramDividend.Classical.avram_p4_f6_hjb_positive_deriv_monotone
      w hw0 hw_cont hd hg).2
  intro y
  rcases lt_or_ge y 0 with hy | hy
  · simp [hw_neg y hy]
  · exact hnonneg y hy
