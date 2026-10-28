-- Prove2me | solution 2 for AvramDividend.Classical.bv_laplace_exponent_finite_jump_rearrangement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:07:11.990983+00:00
-- url     : https://prove2.me/submissions/37376ace-d41d-4d8c-9976-10f143e965e4

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- For finite negative-jump mass, split the BV exponent deficit into
    the total jump intensity and its exponentially tilted component. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (θ : ℝ) (hθ : 1 ≤ θ)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    X.ψ θ = X.drift * θ -
      (X.ν (Iio (0 : ℝ))).toReal +
      ∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂X.ν := by
  let ν : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  haveI : IsFiniteMeasure ν := ⟨by simpa [ν] using hFinite⟩
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) ν := integrable_const 1
  have hmeas : Measurable (fun y : ℝ => Real.exp (θ * y)) :=
    Real.measurable_exp.comp (measurable_const.mul measurable_id)
  have hbound : ∀ᵐ y ∂ν, ‖Real.exp (θ * y)‖ ≤ ‖(1 : ℝ)‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    have hmul : θ * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt hy)
    have he : Real.exp (θ * y) ≤ 1 := (Real.exp_le_one_iff).2 hmul
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using he
  have hexp : Integrable (fun y : ℝ => Real.exp (θ * y)) ν :=
    hone.mono hmeas.aestronglyMeasurable hbound
  have hsplit :
      (∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν) =
        (X.ν (Iio (0 : ℝ))).toReal -
          ∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂X.ν := by
    change (∫ y, (1 - Real.exp (θ * y)) ∂ν) =
      (X.ν (Iio (0 : ℝ))).toReal - ∫ y, Real.exp (θ * y) ∂ν
    rw [integral_sub hone hexp]
    simp [ν, Measure.real_def]
  have hdeficit := bv_exponent_negative_jump_deficit_exact X hBV θ hθ
  rw [hsplit] at hdeficit
  linarith
