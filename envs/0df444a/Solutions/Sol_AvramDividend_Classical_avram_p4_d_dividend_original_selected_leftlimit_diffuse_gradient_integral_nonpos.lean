-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_selected_leftlimit_diffuse_gradient_integral_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:01:11.172371+00:00
-- url     : https://prove2.me/submissions/ef3c0169-64c2-4e92-914b-0687a6056283

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (A : Set ℝ) (hA : MeasurableSet A)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hregion : ∀ᵐ s ∂ν.restrict A,
      0 < (x +
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω) ∧ ENNReal.ofReal (x +
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω) < C)
    (hInt : IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
      (1 - deriv w (x +
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω))) A ν) :
    (∫ s in A, Real.exp (-(q * s)) *
      (1 - deriv w (x +
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω)) ∂ν) ≤ 0 := by
  apply integral_nonpos_of_ae
  filter_upwards [hregion] with s hs
  have hgrad := hw_grad _ hs.1 hs.2
  exact mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (Real.exp_pos _)) (sub_nonpos.mpr hgrad)
