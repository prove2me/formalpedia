-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_jump_convolution_product_integrable_finite_activity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:55:48.793381+00:00
-- url     : https://prove2.me/submissions/d865455d-0ee0-4da8-9da7-96737058b682

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shift_bounds_of_nonpositive
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The weighted jump kernel is product-integrable at finite jump activity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    Integrable (Function.uncurry
      (fun x y : ℝ => Real.exp (-(θ * x)) * W (x + y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))) := by
  letI : IsFiniteMeasure (X.ν.restrict (Iio (0 : ℝ))) := by
    refine ⟨?_⟩
    simpa using hFinite
  have hbase : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * W x)
      (Ioi (0 : ℝ)) := by
    simpa only [add_zero] using
      (scaleFunction_shiftedLaplace_integrable X q W hW θ 0 hθ hqθ le_rfl)
  have hbase' : Integrable
      (fun x : ℝ => Real.exp (-(θ * x)) * W x)
      (volume.restrict (Ioi (0 : ℝ))) := hbase
  have hdom : Integrable
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) * W p.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))) :=
    hbase'.comp_fst (X.ν.restrict (Iio (0 : ℝ)))
  have hWmeas : Measurable W := (scaleFunction_monotone X q W hW).measurable
  have hexp : Measurable
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1))) :=
    Real.measurable_exp.comp ((measurable_const.mul measurable_fst).neg)
  have hfmeas : Measurable
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) * W (p.1 + p.2)) :=
    hexp.mul (hWmeas.comp (measurable_fst.add measurable_snd))
  have hgmeas : Measurable
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) * W p.1) :=
    hexp.mul (hWmeas.comp measurable_fst)
  have hset : MeasurableSet {p : ℝ × ℝ |
      ‖Real.exp (-(θ * p.1)) * W (p.1 + p.2)‖ ≤
        ‖Real.exp (-(θ * p.1)) * W p.1‖} :=
    measurableSet_le hfmeas.norm hgmeas.norm
  have hbound : ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod
      (X.ν.restrict (Iio (0 : ℝ)))),
      ‖Real.exp (-(θ * p.1)) * W (p.1 + p.2)‖ ≤
        ‖Real.exp (-(θ * p.1)) * W p.1‖ := by
    apply (Measure.ae_prod_iff_ae_ae hset).2
    filter_upwards [(ae_restrict_mem (μ := volume) measurableSet_Ioi)] with x hx
    filter_upwards [(ae_restrict_mem (μ := X.ν) measurableSet_Iio)] with y hy
    have hs := scaleFunction_shift_bounds_of_nonpositive X q W hW
      x y (le_of_lt hx) (le_of_lt hy)
    have he : 0 ≤ Real.exp (-(θ * x)) := (Real.exp_pos _).le
    calc
      ‖Real.exp (-(θ * x)) * W (x + y)‖ =
          Real.exp (-(θ * x)) * W (x + y) :=
        Real.norm_of_nonneg (mul_nonneg he hs.1)
      _ ≤ Real.exp (-(θ * x)) * W x :=
        mul_le_mul_of_nonneg_left hs.2 he
      _ = ‖Real.exp (-(θ * x)) * W x‖ :=
        (Real.norm_of_nonneg (mul_nonneg he (le_trans hs.1 hs.2))).symm
  exact hdom.mono hfmeas.aestronglyMeasurable hbound
