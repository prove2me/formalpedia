-- Prove2me | solution 1 for FunctionalInequalities.Energy.Euclidean.hasDerivAt_integral_mul_translate_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:52:14.694985+00:00
-- url     : https://prove2.me/submissions/f959a47d-873a-4a87-ba25-f865465d1466

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
import Theorems.Thm_FunctionalInequalities_Energy_Euclidean_norm_mul_fderiv_comp_sub_smul_le_408915f

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
/-- The derivative of a smooth function along the translation `r ↦ x - r v`. -/
theorem FunctionalInequalities.Energy.Euclidean.hasDerivAt_comp_sub_smul {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (x v : V) (s : ℝ) :
    HasDerivAt (fun r : ℝ => φ (x - r • v)) (-(fderiv ℝ φ (x - s • v) v)) s := by
  have h1 : HasDerivAt (fun r : ℝ => x - r • v) (-v) s := by
    simpa using ((hasDerivAt_id' s).smul_const v).const_sub x
  have h2 :=
    ((hφ.differentiable (by simp)) (x - s • v)).hasFDerivAt.comp_hasDerivAt s h1
  exact h2.congr_deriv (by simp)
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (m : Measure V) [m.IsAddHaarMeasure]
namespace FunctionalInequalities.Energy.Euclidean
end FunctionalInequalities.Energy.Euclidean
open FunctionalInequalities.Energy.Euclidean in
omit [m.IsAddHaarMeasure] in
/-- Differentiation under the integral sign for a translated test: for locally integrable `h`,
`d/dt ∫ h(x) φ(x - t v) dm = -∫ h(x) Dφ(x - t v) v dm`. -/
theorem solution {h : V → ℝ} (hh : LocallyIntegrable h m) {φ : V → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x, h x * φ (x - s • v) ∂m)
      (-∫ x, h x * fderiv ℝ φ (x - t • v) v ∂m) t := by
  obtain ⟨M, hM0, hM⟩ :=
    FunctionalInequalities.Energy.Euclidean.exists_bound_fderiv_of_hasCompactSupport (hφ.of_le (by simp)) hφc
  let K : Set V :=
    Metric.cthickening ((|t| + 1) * ‖v‖) (tsupport φ)
  have hK : IsCompact K := by
    dsimp [K]
    exact hφc.isCompact.cthickening
  have hbound :
      Integrable (K.indicator (fun y => |h y| * (M * ‖v‖))) m := by
    have hi : IntegrableOn (fun y => |h y| * (M * ‖v‖)) K m := by
      change Integrable (fun y => |h y| * (M * ‖v‖)) (m.restrict K)
      simpa [Real.norm_eq_abs] using
        ((hh.integrableOn_isCompact hK).norm.mul_const (M * ‖v‖))
    exact hi.integrable_indicator hK.measurableSet
  have hcont : ∀ r : ℝ, Continuous (fun x : V => φ (x - r • v)) := by
    intro r
    exact hφ.continuous.comp (continuous_id.sub continuous_const)
  have hF_meas :
      ∀ᶠ r in 𝓝 t,
        AEStronglyMeasurable (fun x : V => h x * φ (x - r • v)) m := by
    filter_upwards [] with r
    exact hh.aestronglyMeasurable.mul (hcont r).aestronglyMeasurable
  have hF_int : Integrable (fun x : V => h x * φ (x - t • v)) m := by
    have hi :=
      hh.integrable_smul_left_of_hasCompactSupport
        (g := fun x : V => φ (x - t • v))
        (hcont t)
        (hφc.comp_homeomorph (Homeomorph.subRight (t • v)))
    simpa [smul_eq_mul, mul_comm] using hi
  have hF'_meas :
      AEStronglyMeasurable
        (fun x : V => h x * (-(fderiv ℝ φ (x - t • v) v))) m := by
    have hc : Continuous (fun x : V => fderiv ℝ φ (x - t • v) v) :=
      ((hφ.continuous_fderiv (by simp)).comp
        (continuous_id.sub continuous_const)).clm_apply continuous_const
    exact hh.aestronglyMeasurable.mul hc.neg.aestronglyMeasurable
  have h_bound :
      ∀ᵐ a ∂m, ∀ r ∈ Metric.ball t 1,
        ‖h a * (-(fderiv ℝ φ (a - r • v) v))‖ ≤
          K.indicator (fun y => |h y| * (M * ‖v‖)) a := by
    filter_upwards [] with a r hr
    dsimp [K]
    simpa [norm_mul, norm_neg] using
      (FunctionalInequalities.Energy.Euclidean.norm_mul_fderiv_comp_sub_smul_le_408915f hM h v (Metric.mem_ball.mp hr) a)
  have h_diff :
      ∀ᵐ a ∂m, ∀ r ∈ Metric.ball t 1,
        HasDerivAt
          (fun s : ℝ => h a * φ (a - s • v))
          (h a * (-(fderiv ℝ φ (a - r • v) v))) r := by
    filter_upwards [] with a r hr
    exact (FunctionalInequalities.Energy.Euclidean.hasDerivAt_comp_sub_smul hφ a v r).const_mul (h a)
  have hkey :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := m)
      (F := fun (r : ℝ) (x : V) => h x * φ (x - r • v))
      (F' := fun (r : ℝ) (x : V) => h x * (-(fderiv ℝ φ (x - r • v) v)))
      (x₀ := t)
      (bound := K.indicator (fun y => |h y| * (M * ‖v‖)))
      (s := Metric.ball t 1)
      (Metric.ball_mem_nhds t one_pos)
      hF_meas
      hF_int
      hF'_meas
      h_bound
      hbound
      h_diff
  have h2 := hkey.2
  simp only [mul_neg, integral_neg] at h2
  exact h2
