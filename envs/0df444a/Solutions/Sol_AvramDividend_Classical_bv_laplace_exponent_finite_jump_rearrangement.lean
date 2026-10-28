-- Prove2me | solution 1 for AvramDividend.Classical.bv_laplace_exponent_finite_jump_rearrangement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:04:55.690345+00:00
-- url     : https://prove2.me/submissions/38c2ee83-5a2f-4030-b881-27ba4b625930

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Finite jump mass splits the BV Lévy exponent into drift, mass and moment. -/
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
  letI : IsFiniteMeasure (X.ν.restrict (Iio (0 : ℝ))) := by
    refine ⟨?_⟩
    simpa using hFinite
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ))
      (X.ν.restrict (Iio (0 : ℝ))) := integrable_const _
  have hexpmeas : Measurable (fun y : ℝ => Real.exp (θ * y)) :=
    Real.measurable_exp.comp (measurable_const.mul measurable_id)
  have hexp : Integrable (fun y : ℝ => Real.exp (θ * y))
      (X.ν.restrict (Iio (0 : ℝ))) := by
    apply hconst.mono hexpmeas.aestronglyMeasurable
    filter_upwards [(ae_restrict_mem (μ := X.ν) measurableSet_Iio)] with y hy
    have hθpos : 0 ≤ θ := le_trans zero_le_one hθ
    have hθy : θ * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθpos (le_of_lt hy)
    have hbound : Real.exp (θ * y) ≤ 1 :=
      Real.exp_le_one_iff.mpr hθy
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using hbound
  have hconstval :
      (∫ y in Iio (0 : ℝ), (1 : ℝ) ∂X.ν) =
        (X.ν (Iio (0 : ℝ))).toReal := by
    simp [Measure.real_def]
  have hsub :
      (∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν) =
        (X.ν (Iio (0 : ℝ))).toReal -
          (∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂X.ν) := by
    rw [integral_sub hconst hexp, hconstval]
  have hdef := bv_exponent_negative_jump_deficit_exact X hBV θ hθ
  calc
    X.ψ θ = X.drift * θ -
      (∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν) := by
        linarith
    _ = X.drift * θ -
      ((X.ν (Iio (0 : ℝ))).toReal -
        (∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂X.ν)) := by rw [hsub]
    _ = _ := by ring
