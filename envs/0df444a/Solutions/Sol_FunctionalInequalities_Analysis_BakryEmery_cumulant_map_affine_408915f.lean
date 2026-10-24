-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.cumulant_map_affine_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:42:26.460577+00:00
-- url     : https://prove2.me/submissions/7a4fd3b2-1580-4835-8cf9-cafbfae78239

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section InnerProduct
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.BakryEmery.affine_iteratedFDeriv_linear_eq_zero
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : G →L[ℝ] ℝ) {k : ℕ} (hk : 2 ≤ k) (x : G) :
    iteratedFDeriv ℝ k L x = 0 := by
  have hone :
      iteratedFDeriv ℝ 1 L =
        fun _ : G => iteratedFDeriv ℝ 1 L (0 : G) := by
    funext y
    ext v
    simp only [iteratedFDeriv_one_apply, ContinuousLinearMap.fderiv]
  have hz : ∀ n : ℕ, 2 ≤ n → ∀ y : G, iteratedFDeriv ℝ n L y = 0 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        intro y
        ext v
        change iteratedFDeriv ℝ (1 + 1) L y v = 0
        rw [iteratedFDeriv_succ_apply_left, hone]
        simp
    | succ n _hn ih =>
        have hfun : iteratedFDeriv ℝ n L = fun _ : G => 0 := funext ih
        intro y
        ext v
        change iteratedFDeriv ℝ (n + 1) L y v = 0
        rw [iteratedFDeriv_succ_apply_left, hfun]
        simp
  exact hz k hk x
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **Cumulants along an affine map** (BKL (77)): for `k ≥ 2`, the cumulants of the push-forward of
`μ` under `x ↦ T (x - a)` are those of `μ` evaluated on the adjoint directions,
`κ^{(T(· - a))_*μ}_k(u₁, …, u_k) = κ^μ_k(T† u₁, …, T† u_k)`. -/
theorem solution [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (T : E ≃L[ℝ] F) (a : E) (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {k : ℕ} (hk : 2 ≤ k) (u : Fin k → F) :
    FunctionalInequalities.Analysis.BakryEmery.cumulant (μ.map (fun x => T (x - a))) k u =
      FunctionalInequalities.Analysis.BakryEmery.cumulant μ k (fun i => ContinuousLinearMap.adjoint (T : E →L[ℝ] F) (u i)) := by
  let A : F →L[ℝ] E := ContinuousLinearMap.adjoint (T : E →L[ℝ] F)
  let L : F →L[ℝ] ℝ := (innerSL ℝ a).comp A
  have hL (z : F) : L z = ⟪A z, a⟫ := by
    change ⟪a, A z⟫ = ⟪A z, a⟫
    exact (real_inner_comm a (A z)).symm
  have hadjoint (z : F) (x : E) : ⟪z, T x⟫ = ⟪A z, x⟫ := by
    change ⟪z, (T : E →L[ℝ] F) x⟫ =
      ⟪ContinuousLinearMap.adjoint (T : E →L[ℝ] F) z, x⟫
    simp only [ContinuousLinearMap.adjoint_inner_left]
  have hmeas : Measurable (fun x : E => T (x - a)) :=
    (T.continuous.comp (continuous_id.sub continuous_const)).measurable

  have hlog :
      FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ.map (fun x => T (x - a))) =
        (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ ∘ A) - (L : F → ℝ) := by
    funext z
    have hint : Integrable (fun x : E => Real.exp ⟪A z, x⟫) μ := by
      refine (hexp ‖A z‖).mono'
        ((continuous_const.inner continuous_id).rexp.aestronglyMeasurable) ?_
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (real_inner_le_norm (A z) x)
    have hpos : 0 < ∫ x : E, Real.exp ⟪A z, x⟫ ∂μ :=
      integral_exp_pos hint
    have hfactor :
        (fun x : E => Real.exp ⟪z, T (x - a)⟫) =
          fun x => Real.exp (-L z) * Real.exp ⟪A z, x⟫ := by
      funext x
      rw [hadjoint, inner_sub_right, ← hL z, sub_eq_add_neg, Real.exp_add]
      exact mul_comm _ _
    have hzm :
        AEStronglyMeasurable (fun y : F => Real.exp ⟪z, y⟫)
          (μ.map (fun x => T (x - a))) :=
      (continuous_const.inner continuous_id).rexp.aestronglyMeasurable
    change Real.log (∫ y : F, Real.exp ⟪z, y⟫
      ∂(μ.map (fun x => T (x - a)))) = FunctionalInequalities.Analysis.BakryEmery.logLaplace μ (A z) - L z
    rw [integral_map hmeas.aemeasurable hzm, hfactor, integral_const_mul,
      Real.log_mul (Real.exp_ne_zero _) hpos.ne', Real.log_exp]
    change -L z + FunctionalInequalities.Analysis.BakryEmery.logLaplace μ (A z) = FunctionalInequalities.Analysis.BakryEmery.logLaplace μ (A z) - L z
    ring

  have hΛ : ContDiff ℝ ∞ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) := FunctionalInequalities.Analysis.BakryEmery.contDiff_logLaplace μ hexp
  have hΛk : ContDiff ℝ k (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) :=
    hΛ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg : ContDiff ℝ ∞ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ ∘ A) := hΛ.comp A.contDiff
  have hgk : ContDiff ℝ k (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ ∘ A) := hΛk.comp A.contDiff
  have hl : ContDiff ℝ ∞ (L : F → ℝ) := L.contDiff
  have hlk : ContDiff ℝ k (L : F → ℝ) := L.contDiff

  have hsub :
      iteratedFDeriv ℝ k ((FunctionalInequalities.Analysis.BakryEmery.logLaplace μ ∘ A) - (L : F → ℝ)) (0 : F) =
        iteratedFDeriv ℝ k (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ ∘ A) 0 -
          iteratedFDeriv ℝ k L 0 := by
    have hs :
        iteratedFDeriv ℝ k ((FunctionalInequalities.Analysis.BakryEmery.logLaplace μ ∘ A) - (L : F → ℝ)) =
          iteratedFDeriv ℝ k (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ ∘ A) -
            iteratedFDeriv ℝ k L := by
      apply iteratedFDeriv_sub
      all_goals assumption
    exact congrFun hs (0 : F)

  have hchain :
      iteratedFDeriv ℝ k (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ ∘ A) (0 : F) =
        (iteratedFDeriv ℝ k (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) (A 0)).compContinuousLinearMap
          (fun _ => A) := by
    apply ContinuousLinearMap.iteratedFDeriv_comp_right
    all_goals
      first
      | exact hΛ
      | exact hΛk
      | exact hΛ.contDiffAt
      | exact hΛk.contDiffAt
      | exact le_rfl
      | exact WithTop.coe_le_coe.mpr le_top

  change (iteratedFDeriv ℝ k
      (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ.map (fun x => T (x - a)))) 0) u =
    (iteratedFDeriv ℝ k (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) 0) (fun i => A (u i))
  rw [hlog, hsub, affine_iteratedFDeriv_linear_eq_zero L hk, sub_zero, hchain]
  simp only [map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
