-- Prove2me | solution 1 for FunctionalInequalities.Energy.Euclidean.integral_mul_sub_translate_eq_zero_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:53:14.889105+00:00
-- url     : https://prove2.me/submissions/e60f384c-b29a-431b-88ac-e62810366ed2

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_FunctionalInequalities_Energy_Euclidean_hasDerivAt_integral_mul_translate_408915f

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.Euclidean
end FunctionalInequalities.Energy.Euclidean
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (m : Measure V) [m.IsAddHaarMeasure]
namespace FunctionalInequalities.Energy.Euclidean
end FunctionalInequalities.Energy.Euclidean
open FunctionalInequalities.Energy.Euclidean in
omit [m.IsAddHaarMeasure] in
/-- Zero weak gradient makes `∫ h(x) (φ(x) - φ(x - v)) dm` vanish. -/
theorem solution {h : V → ℝ} (hh : LocallyIntegrable h m)
    (h0 : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ w : V,
      ∫ x, h x * fderiv ℝ φ x w ∂m = 0)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (v : V) :
    ∫ x, h x * (φ x - φ (x - v)) ∂m = 0 := by
  let F : ℝ → ℝ := fun s => ∫ x, h x * φ (x - s • v) ∂m

  have hderiv_translate :
      ∀ s : ℝ, ∀ x : V,
        fderiv ℝ (fun y : V => φ (y - s • v)) x =
          fderiv ℝ φ (x - s • v) := by
    intro s x
    have h1 :
        HasFDerivAt (fun y : V => y - s • v)
          (ContinuousLinearMap.id ℝ V) x :=
      (hasFDerivAt_id x).sub_const (s • v)
    have h2 :=
      ((hφ.differentiable (by simp)) (x - s • v)).hasFDerivAt.comp x h1
    have h2' := h2.fderiv
    have hcomp :
        fderiv ℝ φ (x - s • v) ∘L (ContinuousLinearMap.id ℝ V) =
          fderiv ℝ φ (x - s • v) :=
      ContinuousLinearMap.comp_id _
    exact h2'.trans hcomp

  have hzero : ∀ s : ℝ,
      ∫ x, h x * fderiv ℝ φ (x - s • v) v ∂m = 0 := by
    intro s
    have hψ : ContDiff ℝ ∞ (fun x : V => φ (x - s • v)) :=
      hφ.comp (contDiff_id.sub contDiff_const)
    have hψc : HasCompactSupport (fun x : V => φ (x - s • v)) :=
      hφc.comp_homeomorph (Homeomorph.subRight (s • v))
    have hz := h0 (fun x : V => φ (x - s • v)) hψ hψc v
    simpa only [hderiv_translate s] using hz

  have hder : ∀ s : ℝ,
      HasDerivAt F
        (-(∫ x, h x * fderiv ℝ φ (x - s • v) v ∂m)) s := by
    intro s
    simpa [F] using
      (FunctionalInequalities.Energy.Euclidean.hasDerivAt_integral_mul_translate_408915f m hh hφ hφc v s)

  have hFdiff : Differentiable ℝ F := by
    intro s
    exact (hder s).differentiableAt

  have hFderiv : ∀ s : ℝ, deriv F s = 0 := by
    intro s
    rw [(hder s).deriv, hzero s]
    simp

  have hconst : F 0 = F 1 :=
    is_const_of_deriv_eq_zero hFdiff hFderiv 0 1

  have hF01 :
      (∫ x, h x * φ x ∂m) =
        ∫ x, h x * φ (x - v) ∂m := by
    simpa [F] using hconst

  have hi0 : Integrable (fun x => h x * φ x) m := by
    have hi :=
      hh.integrable_smul_left_of_hasCompactSupport
        (g := φ) hφ.continuous hφc
    simpa [smul_eq_mul, mul_comm] using hi

  have hi1 : Integrable (fun x => h x * φ (x - v)) m := by
    have hφv : Continuous (fun x : V => φ (x - v)) :=
      hφ.continuous.comp (continuous_id.sub continuous_const)
    have hφvc : HasCompactSupport (fun x : V => φ (x - v)) :=
      hφc.comp_homeomorph (Homeomorph.subRight v)
    have hi :=
      hh.integrable_smul_left_of_hasCompactSupport
        (g := fun x : V => φ (x - v)) hφv hφvc
    simpa [smul_eq_mul, mul_comm] using hi

  calc
    ∫ x, h x * (φ x - φ (x - v)) ∂m =
        ∫ x, (h x * φ x - h x * φ (x - v)) ∂m := by
          congr 1
          funext x
          ring
    _ = (∫ x, h x * φ x ∂m) - ∫ x, h x * φ (x - v) ∂m :=
      integral_sub hi0 hi1
    _ = 0 := sub_eq_zero.mpr hF01
