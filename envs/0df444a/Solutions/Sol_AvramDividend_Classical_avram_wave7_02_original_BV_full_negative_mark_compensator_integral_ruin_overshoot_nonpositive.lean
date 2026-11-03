-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_full_negative_mark_compensator_integral_ruin_overshoot_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:12:28.925791+00:00
-- url     : https://prove2.me/submissions/131bfea7-8092-46aa-b45c-8f8b76ce840d

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_source_negative_mark_ruin_overshoot_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Actual original BV negative Lévy source jump compensator has nonpositive
value at every interior predictable controlled reserve, including the entire
ruin-overshooting negative tail and the discount multiplier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (t : ℝ≥0)
    (hregion :
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C)
    (hInt : IntegrableOn (fun z : ℝ =>
      w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t + z) -
      w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))
      (Iio 0) X.ν)
    (q : ℝ) :
    (∫ z in Iio (0 : ℝ),
      w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t + z) -
      w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) ≤ 0 ∧
    Real.exp (-(q * (t : ℝ))) *
      (∫ z in Iio (0 : ℝ),
        w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t + z) -
        w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) ≤ 0 := by
  have hJumpIntegral : (∫ z in Iio (0 : ℝ),
      w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t + z) -
      w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) ≤ 0 := by
    apply MeasureTheory.integral_nonpos_of_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iio] with z hz
    exact sub_nonpos.mpr
      (avram_wave7_02_original_BV_predictable_source_negative_mark_ruin_overshoot_nonpositive
        X C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
        x D ω t hregion z (le_of_lt hz))
  exact ⟨hJumpIntegral,
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _))
      hJumpIntegral⟩
