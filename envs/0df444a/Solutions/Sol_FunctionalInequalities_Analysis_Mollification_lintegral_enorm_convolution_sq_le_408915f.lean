-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Mollification.lintegral_enorm_convolution_sq_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:56:14.627644+00:00
-- url     : https://prove2.me/submissions/2d5babdc-550a-42b6-8e19-a8da66f32d35

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
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
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_enorm_convolution_sq_le_408915f

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Mollification
end FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : Measure V} [m.IsAddHaarMeasure]
section Contraction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (φ : ContDiffBump (0 : V))
namespace FunctionalInequalities.Analysis.Mollification
end FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities.Analysis.Mollification in
/-- The mollifier is an `L²` contraction: `∫ ‖ρ ⋆ f‖² ≤ ∫ ‖f‖²`. -/
theorem solution {f : V → E} (hf : AEStronglyMeasurable f m) :
    ∫⁻ x, ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ^ 2 ∂m ≤
      ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m := by
  have ha : Measurable fun t => ENNReal.ofReal (φ.normed m t) :=
    ENNReal.measurable_ofReal.comp φ.continuous_normed.measurable
  have hmeas : AEMeasurable (fun p : V × V => ENNReal.ofReal (φ.normed m p.2) *
      ‖f (p.1 - p.2)‖ₑ ^ 2) (m.prod m) := by
    refine (ha.comp measurable_snd).aemeasurable.mul ?_
    exact (hf.enorm.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant m m)).pow_const _
  have hint : ∫⁻ t, ENNReal.ofReal (φ.normed m t) ∂m = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
      (Filter.Eventually.of_forall φ.nonneg_normed), φ.integral_normed, ENNReal.ofReal_one]
  calc ∫⁻ x, ‖(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) x‖ₑ ^ 2 ∂m
      ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (φ.normed m t) * ‖f (x - t)‖ₑ ^ 2 ∂m ∂m :=
        lintegral_mono fun x => FunctionalInequalities.Analysis.Mollification.enorm_convolution_sq_le_408915f φ hf x
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (φ.normed m t) * ‖f (x - t)‖ₑ ^ 2 ∂m ∂m :=
        lintegral_lintegral_swap hmeas
    _ = ∫⁻ t, ENNReal.ofReal (φ.normed m t) * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m ∂m := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_sub_right_eq_self (fun x => ‖f x‖ₑ ^ 2) t]
    _ = (∫⁻ t, ENNReal.ofReal (φ.normed m t) ∂m) * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m :=
        lintegral_mul_const _ ha
    _ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m := by rw [hint, one_mul]
