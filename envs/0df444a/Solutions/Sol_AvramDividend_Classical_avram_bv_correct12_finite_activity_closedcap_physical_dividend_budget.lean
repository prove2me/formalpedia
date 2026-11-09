-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_correct12_finite_activity_closedcap_physical_dividend_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T01:24:00.819455+00:00
-- url     : https://prove2.me/submissions/3b0e2706-3038-41a8-b3c0-4a34724985f2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_uniform_fullcap_candidate_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_compact_stopped_full_right_dividend_C1_pathwise_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Original stopped right-dividend budget including the upper cap endpoint. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (b : ℝ) (hb : 0 ≤ b) (hbC : ENNReal.ofReal b ≤ C) :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
        x + X.X s ω - rightLimit D s ω ∈ Icc 0 b →
        x + X.X t ω - rightLimit D t ω ∈ Icc 0 b →
        (rightLimit D t ω - rightLimit D s ω) +
          (w (x + X.X t ω - rightLimit D t ω) -
            w (x + X.X s ω - rightLimit D s ω)) ≤
          L * (((t : ℝ) - (s : ℝ)) * X.drift) := by
  classical
  obtain ⟨L₀, _hL₀, hUpper⟩ :=
    avram_bv_correct12_finite_activity_uniform_fullcap_candidate_lipschitz
      X hX hBV hFinite q hq w C hC hw_cont hw0 hw_neg
      hw_smooth hw_gen hw_grad b hb hbC
  let L : ℝ := max 1 L₀
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLupper : L₀ ≤ L := le_max_right _ _
  have hNonneg : ∀ y z : ℝ, 0 ≤ y → y ≤ z → z ≤ b →
      0 ≤ w z - w y := by
    intro y z hy hyz hzb
    have hzC : ENNReal.ofReal z ≤ C :=
      (ENNReal.ofReal_le_ofReal hzb).trans hbC
    have hSec := avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad y z hy hyz hzC
    exact (sub_nonneg.mpr hyz).trans hSec
  have hLip : ∀ y ∈ Icc (0 : ℝ) b, ∀ z ∈ Icc (0 : ℝ) b,
      |w y - w z| ≤ L * |y - z| := by
    intro y hy z hz
    rcases le_total y z with hyz | hzy
    · have hDiff : 0 ≤ w z - w y :=
        hNonneg y z hy.1 hyz hz.2
      have hBound := hUpper y z hy.1 hyz hz.2
      calc
        |w y - w z| = w z - w y := by
          rw [abs_sub_comm, abs_of_nonneg hDiff]
        _ ≤ L₀ * (z - y) := hBound
        _ ≤ L * (z - y) :=
          mul_le_mul_of_nonneg_right hLupper (sub_nonneg.mpr hyz)
        _ = L * |y - z| := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hyz)]
    · have hDiff : 0 ≤ w y - w z :=
        hNonneg z y hz.1 hzy hy.2
      have hBound := hUpper z y hz.1 hzy hy.2
      calc
        |w y - w z| = w y - w z := abs_of_nonneg hDiff
        _ ≤ L₀ * (y - z) := hBound
        _ ≤ L * (y - z) :=
          mul_le_mul_of_nonneg_right hLupper (sub_nonneg.mpr hzy)
        _ = L * |y - z| := by
          rw [abs_of_nonneg (sub_nonneg.mpr hzy)]
  exact ⟨L, hL1,
    avram_wave7_02_original_BV_compact_stopped_full_right_dividend_C1_pathwise_budget
      X hX hBV x D hD C hC w hw_cont hw_smooth hw_grad
      0 b L (le_refl 0) hb hbC hL1 hLip⟩
