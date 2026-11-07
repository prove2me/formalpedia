-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_turn16_scalar_ode_exponential_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:43:23.662985+00:00
-- url     : https://prove2.me/submissions/278b1950-ae42-42e3-a72c-7c71f4c4601c

import Mathlib.Tactic
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn16_two_real_characteristic_roots_v2
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn16_factorised_ode_upper_exponential_comparison_v2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal


noncomputable section

theorem solution
    (a c q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (ha : 0 < a) (hq : 0 < q) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hode : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      a * iteratedDeriv 2 w y + c * deriv w y - q * w y ≤ 0) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, w y ≤ K * Real.exp (θ * y) := by
  obtain ⟨rpos, rneg, hrpos, hrneg, hsum, hprod⟩ :=
    AvramDividend.Classical.avram_p4_f4_turn16_two_real_characteristic_roots_v2
      a c q ha hq
  have hFac : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      iteratedDeriv 2 w y - (rpos + rneg) * deriv w y + rpos * rneg * w y ≤ 0 := by
    intro y hy hCy
    have hEq :
        a * (iteratedDeriv 2 w y - (rpos + rneg) * deriv w y +
          rpos * rneg * w y) =
        a * iteratedDeriv 2 w y + c * deriv w y - q * w y := by
      calc
        _ = a * iteratedDeriv 2 w y -
              (a * (rpos + rneg)) * deriv w y +
              (a * (rpos * rneg)) * w y := by ring
        _ = a * iteratedDeriv 2 w y + c * deriv w y - q * w y := by
          rw [hsum, hprod]
          ring
    have hScaled :
        a * (iteratedDeriv 2 w y - (rpos + rneg) * deriv w y +
          rpos * rneg * w y) ≤ 0 := by
      rw [hEq]
      exact hode y hy hCy
    by_contra hn
    have hPos : 0 < iteratedDeriv 2 w y -
          (rpos + rneg) * deriv w y + rpos * rneg * w y := lt_of_not_ge hn
    have hMul : 0 < a * (iteratedDeriv 2 w y -
          (rpos + rneg) * deriv w y + rpos * rneg * w y) := mul_pos ha hPos
    linarith
  obtain ⟨K, hK, hGrowth⟩ :=
    AvramDividend.Classical.avram_p4_f4_turn16_factorised_ode_upper_exponential_comparison_v2
      rpos rneg hrpos hrneg w C hTop hw0 hw_cont hw_neg hw_smooth hFac
  exact ⟨rpos, K, le_of_lt hrpos, hK, hGrowth⟩
