-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_infinitecap_candidate_globally_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:31:37.141951+00:00
-- url     : https://prove2.me/submissions/1b17c872-f22e-4bb3-9db8-5697d24c292e

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Top-cap HJB gradient positivity extends the nonnegative value
    from the zero boundary to all real reserves, including ruin overshoots. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hCtop : C = ⊤) :
    ∀ y : ℝ, 0 ≤ w y := by
  intro y
  by_cases hneg : y < 0
  · rw [hw_neg y hneg]
  · have hy : 0 ≤ y := le_of_not_gt hneg
    have hC1 : ContDiffOn ℝ 1 w
        {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} :=
      hw_smooth.of_le (by norm_num)
    have hcy : ENNReal.ofReal y < C := by
      simp [hCtop]
    have hInterval :=
      avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
        C hC w hw_cont hw0 hC1 hw_grad y hy hcy
    exact hInterval y ⟨hy, le_rfl⟩
