-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_stopped_C1_compact_upward_value_drift_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:50:12.618939+00:00
-- url     : https://prove2.me/submissions/03157bcd-ae22-45b8-afe0-68e908dd8699

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Genuine BV stopped postpayment C1 value has at most physical upward
drift rate on a compact positive-cap localisation strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbC : ENNReal.ofReal b ≤ C)
    (hL : 0 ≤ L) (hd : 0 ≤ X.drift)
    (hLip : ∀ y ∈ Icc a b, ∀ z ∈ Icc a b,
      |w y - w z| ≤ L * |y - z|) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      x + X.X s ω - rightLimit D s ω ∈ Icc a b →
      x + X.X t ω - rightLimit D t ω ∈ Icc a b →
      w (x + X.X t ω - rightLimit D t ω) -
        w (x + X.X s ω - rightLimit D s ω) ≤
          L * (((t : ℝ) - (s : ℝ)) * X.drift) := by
  filter_upwards
    [avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
      X hBV x D hD] with ω hInc
  intro s t hst hsBand htBand
  let ys : ℝ := x + X.X s ω - rightLimit D s ω
  let yt : ℝ := x + X.X t ω - rightLimit D t ω
  have hYs : ys ∈ Icc a b := hsBand
  have hYt : yt ∈ Icc a b := htBand
  have hYsNonneg : 0 ≤ ys := le_trans ha hYs.1
  have hYtNonneg : 0 ≤ yt := le_trans ha hYt.1
  have hYsCap : ENNReal.ofReal ys ≤ C :=
    (ENNReal.ofReal_le_ofReal hYs.2).trans hbC
  have hYtCap : ENNReal.ofReal yt ≤ C :=
    (ENNReal.ofReal_le_ofReal hYt.2).trans hbC
  have hIncrement := hInc s t hst
  change yt - ys ≤ ((t : ℝ) - (s : ℝ)) * X.drift at hIncrement
  have hTime : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
  have hPhysical : 0 ≤ ((t : ℝ) - (s : ℝ)) * X.drift :=
    mul_nonneg (sub_nonneg.mpr hTime) hd
  change w yt - w ys ≤ L * (((t : ℝ) - (s : ℝ)) * X.drift)
  by_cases hDown : yt ≤ ys
  · have hSec := avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad yt ys
      hYtNonneg hDown hYsCap
    have hValue : w yt ≤ w ys := by linarith
    have hUp : 0 ≤ L * (((t : ℝ) - (s : ℝ)) * X.drift) :=
      mul_nonneg hL hPhysical
    linarith
  · have hUpReserve : ys ≤ yt := le_of_lt (lt_of_not_ge hDown)
    have hSec := avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad ys yt
      hYsNonneg hUpReserve hYtCap
    have hValue : w ys ≤ w yt := by linarith
    have hLipBound := hLip yt hYt ys hYs
    rw [abs_of_nonneg (sub_nonneg.mpr hValue),
      abs_of_nonneg (sub_nonneg.mpr hUpReserve)] at hLipBound
    have hRate := mul_le_mul_of_nonneg_left hIncrement hL
    linarith
