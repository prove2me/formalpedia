-- Prove2me | solution 1 for FunctionalInequalities.Analysis.quotient_pairing_tendsto_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:16:39.722612+00:00
-- url     : https://prove2.me/submissions/7e1aea78-989b-4e62-9519-497664f191cd

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.Pi

noncomputable section
open MeasureTheory
open scoped ContDiff
section LN11C1WeakDerivativeOfDifferenceBound
open MeasureTheory Set Filter
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]
private lemma FunctionalInequalities.Analysis.translated_memLp {f : E → ℝ}
    (hf : MemLp f 2 (volume : Measure E)) (w : E) :
    MemLp (fun x => f (x - w)) 2 (volume : Measure E) := by
  simpa only [Function.comp_def, sub_eq_add_neg] using
    hf.comp_measurePreserving (measurePreserving_add_right volume (-w))
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
 lemma solution {f : E → ℝ}
    (hf : MemLp f 2 (volume : Measure E)) (v : E)
    {ψ : E → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    Tendsto
      (fun t : ℝ => ∫ x, (t⁻¹ * (f (x - t • v) - f x)) * ψ x)
      (𝓝[≠] 0) (𝓝 (∫ x, f x * fderiv ℝ ψ x v)) := by
  let F : ℝ → ℝ := fun t =>
    convolution (fun y => f (-y)) ψ (ContinuousLinearMap.mul ℝ ℝ) volume (t • v)
  have hi : LocallyIntegrable (fun y => f (-y)) (volume : Measure E) :=
    (hf.comp_measurePreserving (Measure.measurePreserving_neg volume)).locallyIntegrable
      (by norm_num)
  have hF (t : ℝ) : F t = ∫ x, f (x - t • v) * ψ x := by
    have h := integral_sub_left_eq_self
      (fun y => f (-y) * ψ (t • v - y)) (volume : Measure E) (t • v)
    simpa only [F, convolution_def, ContinuousLinearMap.mul_apply',
      neg_sub, sub_sub_cancel] using h.symm
  have hd : HasDerivAt F (∫ x, f x * fderiv ℝ ψ x v) 0 := by
    have h :=
      (hψc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
        hi hψ (0 • v)).comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const v)
    simp only [one_smul, zero_smul] at h
    apply h.congr_deriv
    calc
      _ = convolution (fun y => f (-y)) (fun x => fderiv ℝ ψ x v)
          (ContinuousLinearMap.mul ℝ ℝ) volume 0 :=
        convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hi
          (hψc.fderiv ℝ) (hψ.continuous_fderiv one_ne_zero) 0 v
      _ = ∫ x, f x * fderiv ℝ ψ x v := by
        simpa only [convolution_def, ContinuousLinearMap.mul_apply', zero_sub] using
          integral_neg_eq_self (fun x => f x * fderiv ℝ ψ x v) volume
  have hp : MemLp ψ 2 (volume : Measure E) :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  have heq (t : ℝ) :
      (∫ x, (t⁻¹ * (f (x - t • v) - f x)) * ψ x) =
        t⁻¹ * (F t - F 0) := by
    have i₁ : Integrable (fun x => f (x - t • v) * ψ x)
        (volume : Measure E) :=
      (translated_memLp hf (t • v)).integrable_mul hp
    have i₀ : Integrable (fun x => f x * ψ x) (volume : Measure E) :=
      hf.integrable_mul hp
    rw [hF t, hF 0]
    simp only [zero_smul, sub_zero]
    calc
      _ = ∫ x, t⁻¹ * (f (x - t • v) * ψ x - f x * ψ x) := by
        apply integral_congr_ae
        exact .of_forall (fun x => by ring)
      _ = _ := by
        rw [integral_const_mul, integral_sub i₁ i₀]
  have ht := hd.tendsto_slope_zero
  simp only [zero_add, smul_eq_mul] at ht
  exact ht.congr' (.of_forall fun t => (heq t).symm)
