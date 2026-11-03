-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_compact_stopped_full_right_dividend_C1_pathwise_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:28:50.968251+00:00
-- url     : https://prove2.me/submissions/ea089936-a796-405d-a958-d1e4bca64980

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Actual BV source plus the full right-dividend cumulative increment.
On a compact pre-ruin localisation strip, the C1 value and all payouts have
one pathwise drift envelope, including diffuse and singular-continuous parts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbC : ENNReal.ofReal b ≤ C)
    (hL1 : 1 ≤ L)
    (hLip : ∀ y ∈ Icc a b, ∀ z ∈ Icc a b,
      |w y - w z| ≤ L * |y - z|) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      x + X.X s ω - rightLimit D s ω ∈ Icc a b →
      x + X.X t ω - rightLimit D t ω ∈ Icc a b →
      (rightLimit D t ω - rightLimit D s ω) +
        (w (x + X.X t ω - rightLimit D t ω) -
          w (x + X.X s ω - rightLimit D s ω)) ≤
        L * (((t : ℝ) - (s : ℝ)) * X.drift) := by
  have hd : 0 ≤ X.drift := (bv_standing_drift_pos X hX hBV).1.le
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL1
  filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV] with ω hR
  intro s t hst hsBand htBand
  let ys : ℝ := x + X.X s ω - rightLimit D s ω
  let yt : ℝ := x + X.X t ω - rightLimit D t ω
  have hys : ys ∈ Icc a b := hsBand
  have hyt : yt ∈ Icc a b := htBand
  have hys0 : 0 ≤ ys := le_trans ha hys.1
  have hyt0 : 0 ≤ yt := le_trans ha hyt.1
  have hysC : ENNReal.ofReal ys ≤ C :=
    (ENNReal.ofReal_le_ofReal hys.2).trans hbC
  have hytC : ENNReal.ofReal yt ≤ C :=
    (ENNReal.ofReal_le_ofReal hyt.2).trans hbC
  have hSource : X.X t ω - X.X s ω ≤
      ((t : ℝ) - (s : ℝ)) * X.drift := by
    have hOrig := hR hst
    dsimp at hOrig
    nlinarith
  have hPay : 0 ≤ rightLimit D t ω - rightLimit D s ω := by
    exact sub_nonneg.mpr
      (avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω hst)
  have hEq : (rightLimit D t ω - rightLimit D s ω) +
      (yt - ys) = X.X t ω - X.X s ω := by
    dsimp [yt, ys]
    ring
  have hstR : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
  have hPhysical : 0 ≤ ((t : ℝ) - (s : ℝ)) * X.drift :=
    mul_nonneg (sub_nonneg.mpr hstR) hd
  change (rightLimit D t ω - rightLimit D s ω) +
    (w yt - w ys) ≤ L * (((t : ℝ) - (s : ℝ)) * X.drift)
  by_cases hDown : yt ≤ ys
  · have hSec := avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad yt ys hyt0 hDown hysC
    have hDrop : w yt - w ys ≤ yt - ys := by linarith
    have hBudget : (rightLimit D t ω - rightLimit D s ω) +
        (w yt - w ys) ≤ ((t : ℝ) - (s : ℝ)) * X.drift := by
      linarith
    have hScale : ((t : ℝ) - (s : ℝ)) * X.drift ≤
        L * (((t : ℝ) - (s : ℝ)) * X.drift) := by
      have hNonneg := mul_nonneg (sub_nonneg.mpr hL1) hPhysical
      nlinarith
    exact le_trans hBudget hScale
  · have hUp : ys ≤ yt := le_of_lt (lt_of_not_ge hDown)
    have hSec := avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad ys yt hys0 hUp hytC
    have hVal : w ys ≤ w yt := by linarith
    have hLipBound := hLip yt hyt ys hys
    rw [abs_of_nonneg (sub_nonneg.mpr hVal),
      abs_of_nonneg (sub_nonneg.mpr hUp)] at hLipBound
    have hCombined : (rightLimit D t ω - rightLimit D s ω) +
        (yt - ys) ≤ ((t : ℝ) - (s : ℝ)) * X.drift := by
      linarith
    have hScaled := mul_le_mul_of_nonneg_left hCombined hL0
    have hPayScaled : rightLimit D t ω - rightLimit D s ω ≤
        L * (rightLimit D t ω - rightLimit D s ω) := by
      have hNonneg := mul_nonneg (sub_nonneg.mpr hL1) hPay
      nlinarith
    nlinarith
