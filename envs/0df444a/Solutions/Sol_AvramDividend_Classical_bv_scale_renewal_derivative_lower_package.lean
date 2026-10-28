-- Prove2me | solution 1 for AvramDividend.Classical.bv_scale_renewal_derivative_lower_package
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:18:28.382878+00:00
-- url     : https://prove2.me/submissions/8a2374a9-344a-49e8-99d2-0b51957443bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_scale_origin_eq_inv_drift
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_family_from_scale_20261026
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero
import Theorems.Thm_AvramDividend_Classical_levy_negative_mass_away_from_zero_finite
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_interval_harmonic_of_laplace_family
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation) :
    W 0 = 1 / X.drift ∧
      ∀ x : ℝ, 0 < x → ∃ R : ℝ,
        0 ≤ R ∧
          X.drift * deriv W x =
            q * W x + (X.ν (Iio (-x))).toReal * W 0 + R := by
  refine ⟨bv_scale_origin_eq_inv_drift X hX q hq W hW hBV, ?_⟩
  intro x hx
  have hC1 := scaleFunction_contDiffOn_one_of_boundedVariation X hX q hq W hW hBV
  have hint : X.GeneratorIntegrable W x :=
    scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one X q W hW hBV x hx hC1
  have hharm := scaleFunction_generator_interval_harmonic_of_laplace_family X hX q hq W hW
    (x + 1) (by linarith)
    (generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero X hX hBV hBV.1 q W hW hC1)
    (bv_weighted_generator_residual_family_from_scale_20261026 X hX hBV q hq W hW)
    (fun z hz => scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one X q W hW hBV z
      hz.1 hC1) x ⟨hx, by linarith⟩
  have hrep := boundedVariation_generator_physical_drift_representation X hBV W x hint
  -- integrability of the jump increment
  have hsmall : IntegrableOn (fun y : ℝ => y * (Ioo (-1 : ℝ) 1).indicator 1 y) (Iio 0) X.ν := by
    have h1 : IntegrableOn (fun y : ℝ => y) (Ioo (-1 : ℝ) 0) X.ν := by
      refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      calc (∫⁻ y in Ioo (-1 : ℝ) 0, ‖y‖ₑ ∂X.ν)
          = ∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν := by
            congr 1; ext y; rw [Real.enorm_eq_ofReal_abs]
        _ < ⊤ := hBV.2
    have h2 : IntegrableOn ((Ioo (-1 : ℝ) 0).indicator (fun y : ℝ => y)) (Iio 0) X.ν :=
      (h1.integrable_indicator measurableSet_Ioo).integrableOn
    refine h2.congr_fun (fun y hy => ?_) measurableSet_Iio
    have hy' : y < 0 := hy
    by_cases h : -1 < y
    · rw [indicator_of_mem (show y ∈ Ioo (-1 : ℝ) 0 from ⟨h, hy'⟩),
        indicator_of_mem (show y ∈ Ioo (-1 : ℝ) 1 from ⟨h, by linarith⟩)]
      simp
    · rw [indicator_of_notMem (show y ∉ Ioo (-1 : ℝ) 0 from fun h' => h h'.1),
        indicator_of_notMem (show y ∉ Ioo (-1 : ℝ) 1 from fun h' => h h'.1)]
      simp
  have hf : IntegrableOn (fun y : ℝ => W x - W (x + y)) (Iio 0) X.ν := by
    have := (hint.add (hsmall.const_mul (deriv W x))).neg
    refine this.congr_fun (fun y _ => ?_) measurableSet_Iio
    simp only [SpectrallyNegativeLevy.generatorIntegrand, Pi.neg_apply, Pi.add_apply]
    ring
  have hfin : X.ν (Iio (-x)) < ⊤ :=
    lt_of_le_of_lt (measure_mono Iio_subset_Iic_self)
      (levy_negative_mass_away_from_zero_finite X x hx)
  have hg : IntegrableOn ((Iio (-x)).indicator (fun _ : ℝ => W 0)) (Iio 0) X.ν := by
    apply Integrable.integrableOn
    rw [integrable_indicator_iff measurableSet_Iio]
    exact integrableOn_const hfin.ne
  have hmono : ∫ y in Iio (0 : ℝ), (Iio (-x)).indicator (fun _ : ℝ => W 0) y ∂X.ν ≤
      ∫ y in Iio (0 : ℝ), (W x - W (x + y)) ∂X.ν := by
    apply setIntegral_mono_on hg hf measurableSet_Iio
    intro y hy
    have hy' : y < 0 := hy
    by_cases h : y < -x
    · rw [indicator_of_mem (show y ∈ Iio (-x) from h), hW.1 (x + y) (by linarith)]
      have := hW.2.2.2.1 (show (0 : ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) (show x ∈ Ici (0 : ℝ) from hx.le)
        hx.le
      linarith
    · rw [indicator_of_notMem (show y ∉ Iio (-x) from h)]
      have := hW.2.2.2.1 (show x + y ∈ Ici (0 : ℝ) from by simp only [mem_Ici]; push Not at h; linarith)
        (show x ∈ Ici (0 : ℝ) from hx.le) (by linarith)
      linarith
  have hleft : ∫ y in Iio (0 : ℝ), (Iio (-x)).indicator (fun _ : ℝ => W 0) y ∂X.ν =
      (X.ν (Iio (-x))).toReal * W 0 := by
    rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      setIntegral_const, smul_eq_mul]
    rw [show Iio (-x) ∩ Iio (0 : ℝ) = Iio (-x) from
      inter_eq_left.mpr (Iio_subset_Iio (by linarith))]
    rfl
  refine ⟨(∫ y in Iio (0 : ℝ), (W x - W (x + y)) ∂X.ν) - (X.ν (Iio (-x))).toReal * W 0,
    by linarith, ?_⟩
  have hneg : ∫ y in Iio (0 : ℝ), (W x - W (x + y)) ∂X.ν =
      -∫ y in Iio (0 : ℝ), (W (x + y) - W x) ∂X.ν := by
    rw [← integral_neg]; congr 1; ext y; ring
  have h0 := hharm.2
  rw [hrep] at h0
  rw [hneg]
  linarith
