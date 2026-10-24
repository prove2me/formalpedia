-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing_parts_vol
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:43:04.505453+00:00
-- url     : https://prove2.me/submissions/e53f568d-ff16-42ff-aac2-0fad6c7e2f15

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq_signed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Equal transforms of both signed parts force the generator residual to vanish. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (b : ℝ)
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioi 0))
    (hpart : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
        max (X.generator W x - q * W x) 0) (Ioi (0 : ℝ)) (volume : Measure ℝ) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
        max (-(X.generator W x - q * W x)) 0) (Ioi (0 : ℝ)) (volume : Measure ℝ) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
        max (X.generator W x - q * W x) 0) =
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
        max (-(X.generator W x - q * W x)) 0)) :
    ∀ᵐ x ∂(volume.restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0 := by
  let R : ℝ → ℝ := fun x => X.generator W x - q * W x
  have max_continuous (f : ℝ → ℝ)
      (hf : ContinuousOn f (Ioi 0)) :
      ContinuousOn (fun x => max (f x) 0) (Ioi 0) := by
    have habs : ContinuousOn (fun x => |f x|) (Ioi 0) := hf.abs
    have haux : ContinuousOn (fun x => (f x + |f x|) / 2) (Ioi 0) :=
      (hf.add habs).div_const 2
    have heq : (fun x => max (f x) 0) =
        (fun x => (f x + |f x|) / 2) := by
      funext x
      rcases le_total (f x) 0 with hn | hp
      · rw [max_eq_right hn, abs_of_nonpos hn]
        ring
      · rw [max_eq_left hp, abs_of_nonneg hp]
        ring
    rw [heq]
    exact haux
  have hpos : ContinuousOn (fun x => max (R x) 0) (Ioi 0) :=
    max_continuous R hcont
  have hneg : ContinuousOn (fun x => max (-(R x)) 0) (Ioi 0) :=
    max_continuous (fun x => -(R x)) hcont.neg
  have heq : ∀ x : ℝ, 0 < x →
      max (R x) 0 = max (-(R x)) 0 :=
    continuousOn_Ioi_eq_of_laplace_eq_signed
      (fun x => max (R x) 0) (fun x => max (-(R x)) 0)
      b hpos hneg hpart
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have h := heq x hx.1
  change R x = 0
  rcases le_total (R x) 0 with hn | hp
  · rw [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)] at h
    linarith
  · rw [max_eq_left hp, max_eq_right (neg_nonpos.mpr hp)] at h
    linarith
