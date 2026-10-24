-- Prove2me | solution 1 for FunctionalInequalities.Analysis.sum_integral_adjugate_hessianMatrix_mul_fderiv_eq_zero_of_lipschitz_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:06:39.791378+00:00
-- url     : https://prove2.me/submissions/5c50215a-aea6-4d81-bba3-5a579dc82fb2

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Piola
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_FunctionalInequalities_Analysis_exists_contDiff_approx_of_lipschitz_gradient_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_sum_fderiv_adjugate_hessianMatrix_eq_zero_408915f

noncomputable section
open Matrix
open FunctionalInequalities.Probability.Stein
section LN10AInverseHessianDivergence
open MeasureTheory Set Filter
open scoped Topology
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section NormedSpace
variable [NormedSpace ℝ E]
private lemma FunctionalInequalities.Analysis.n10_measurable_deriv
    [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (v : E) :
    Measurable (fun x => fderiv ℝ f x v) :=
  (ContinuousLinearMap.apply ℝ ℝ v).measurable.comp (measurable_fderiv ℝ f)
private lemma FunctionalInequalities.Analysis.n10_deriv_bound
    {f : E → ℝ} {L : NNReal} (hf : LipschitzWith L f) (v x : E) :
    ‖fderiv ℝ f x v‖ ≤ (L : ℝ) * ‖v‖ :=
  (fderiv ℝ f x).le_opNorm v |>.trans
    (mul_le_mul_of_nonneg_right
      (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v))
private lemma FunctionalInequalities.Analysis.n10_deriv_zero
    {f : E → ℝ} {x : E} (hx : x ∉ tsupport f) (v : E) :
    fderiv ℝ f x v = 0 := by
  have hz : fderiv ℝ f x = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hx ((tsupport_fderiv_subset ℝ) h))
  rw [hz]
  rfl
end NormedSpace
section FiniteDimensional
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
section MeasurableSpace
variable [MeasurableSpace E] [BorelSpace E]
private lemma FunctionalInequalities.Analysis.n10_integrable_bounded_compact
    {f : E → ℝ} (hm : Measurable f) (hc : HasCompactSupport f)
    {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) :
    Integrable f (volume : Measure E) := by
  have hl : LocallyIntegrable f (volume : Measure E) :=
    (memLp_top_of_bound hm.aestronglyMeasurable C
      (Eventually.of_forall hb)).locallyIntegrable le_top
  exact (hl.integrableOn_isCompact hc.isCompact).integrable_of_forall_notMem_eq_zero
    (fun _ hx => image_eq_zero_of_notMem_tsupport hx)
private lemma FunctionalInequalities.Analysis.n10_integrable_deriv
    {f : E → ℝ} {L : NNReal} (hf : LipschitzWith L f)
    (hc : HasCompactSupport f) (v : E) :
    Integrable (fun x => fderiv ℝ f x v) (volume : Measure E) :=
  n10_integrable_bounded_compact (n10_measurable_deriv f v)
    (hc.fderiv_apply ℝ v) (n10_deriv_bound hf v)
end MeasurableSpace
private lemma FunctionalInequalities.Analysis.n10_cutoff
    {K : Set E} (hK : IsCompact K) :
    ∃ χ : E → ℝ, ContDiff ℝ 1 χ ∧ HasCompactSupport χ ∧
      ∀ x ∈ K, χ =ᶠ[𝓝 x] (fun _ => 1) := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : E)
  let φ : ContDiffBump (0 : E) :=
    ⟨max r 0 + 1, max r 0 + 2, by positivity, by linarith⟩
  refine ⟨φ, φ.contDiff, φ.hasCompactSupport, ?_⟩
  intro x hx
  apply φ.eventuallyEq_one_of_mem_ball
  have h := hr hx
  change dist x 0 ≤ r at h
  change dist x 0 < max r 0 + 1
  linarith [le_max_left r 0]
end FiniteDimensional
/-- Localization lets Lipschitz integration by parts act on a smooth coefficient. -/
private lemma FunctionalInequalities.Analysis.n10_integration_by_parts {n : ℕ}
    {f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 1 f) {L : NNReal} (hψ : LipschitzWith L ψ)
    (hψc : HasCompactSupport ψ) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, f x * fderiv ℝ ψ x v) =
      - ∫ x, fderiv ℝ f x v * ψ x := by
  obtain ⟨χ, hχ, hχc, hχeq⟩ := n10_cutoff hψc.isCompact
  let g := fun x => χ x * f x
  have hgd : ContDiff ℝ 1 g := hχ.mul hf
  have hgc : HasCompactSupport g := hχc.mul_right
  obtain ⟨D, hg⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hgd one_ne_zero
  have heq (x) (hx : x ∈ tsupport ψ) : g =ᶠ[𝓝 x] f := by
    filter_upwards [hχeq x hx] with y hy
    change χ y * f y = f y
    rw [hy, one_mul]
  have hb := hg.integral_lineDeriv_mul_eq
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hψ hψc v
  have hl :
      (∫ x, lineDeriv ℝ g x v * ψ x) =
        ∫ x, fderiv ℝ f x v * ψ x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change lineDeriv ℝ g x v * ψ x = fderiv ℝ f x v * ψ x
      rw [(hgd.differentiable one_ne_zero x).lineDeriv_eq_fderiv]
      by_cases hx : x ∈ tsupport ψ
      · rw [(heq x hx).fderiv_eq]
      · rw [image_eq_zero_of_notMem_tsupport hx]
        simp
  have hr :
      (∫ x, lineDeriv ℝ ψ x (-v) * g x) =
        -(∫ x, f x * fderiv ℝ ψ x v) := by
    calc
      (∫ x, lineDeriv ℝ ψ x (-v) * g x) =
          ∫ x, -(f x * fderiv ℝ ψ x v) := by
        apply integral_congr_ae
        filter_upwards [hψ.ae_differentiableAt
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))] with x hxD
        rw [hxD.lineDeriv_eq_fderiv, map_neg]
        by_cases hx : x ∈ tsupport ψ
        · rw [(heq x hx).eq_of_nhds]
          ring
        · rw [n10_deriv_zero hx v]
          simp
      _ = _ := integral_neg _
  rw [hl, hr] at hb
  linarith
private lemma FunctionalInequalities.Analysis.n10_hessian {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix u x = FunctionalInequalities.Analysis.n10_matrix (fderiv ℝ (gradient u) x) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  have he : fderiv ℝ u = T ∘ gradient u :=
    funext fun y => (T.apply_symm_apply (fderiv ℝ u y)).symm
  have hd :
      fderiv ℝ (fderiv ℝ u) x =
        T.toContinuousLinearMap.comp (fderiv ℝ (gradient u) x) :=
    (congrArg (fun f => fderiv ℝ f x) he).trans T.comp_fderiv
  ext r s
  change
    fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.basisFun (Fin n) ℝ r)
        (EuclideanSpace.basisFun (Fin n) ℝ s) =
      T (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ r))
        (EuclideanSpace.basisFun (Fin n) ℝ s)
  rw [hd]
  rfl
private lemma FunctionalInequalities.Analysis.n10_continuous_cofactor {n : ℕ} (i j : Fin n) :
    Continuous
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
        (FunctionalInequalities.Analysis.n10_matrix L).adjugate i j) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  apply (continuous_apply j).comp
  apply (continuous_apply i).comp
  apply Continuous.matrix_adjugate
  apply continuous_pi
  intro r
  apply continuous_pi
  intro s
  exact
    (T.continuous.comp (continuous_id.clm_apply continuous_const)).clm_apply
      continuous_const
private lemma FunctionalInequalities.Analysis.n10_measurable_cofactor {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (i j : Fin n) :
    Measurable (fun x => (hessianMatrix u x).adjugate i j) := by
  simpa only [n10_hessian, Function.comp_def] using
    (n10_continuous_cofactor i j).measurable.comp
      (measurable_fderiv ℝ (gradient u))
private lemma FunctionalInequalities.Analysis.n10_contDiff_cofactor {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 3 u)
    (i j : Fin n) :
    ContDiff ℝ 1 (fun x => (hessianMatrix u x).adjugate i j) := by
  classical
  have h₂ : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have h₁ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    h₂.fderiv_right (by norm_num)
  have hentry : ∀ r s, ContDiff ℝ 1 (fun x => hessianMatrix u x r s) := by
    intro r s
    exact (h₁.clm_apply contDiff_const).clm_apply contDiff_const
  simp only [Matrix.adjugate_apply, Matrix.det_apply]
  apply ContDiff.sum
  intro σ _
  apply ContDiff.const_smul
  apply contDiff_prod
  intro r _
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact hentry _ _
private lemma FunctionalInequalities.Analysis.n10_smooth_piola {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 3 u)
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hψ : LipschitzWith L ψ) (hψc : HasCompactSupport ψ) (i : Fin n) :
    ∑ j, ∫ x, (hessianMatrix u x).adjugate i j *
      fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j) = 0 := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hA := n10_contDiff_cofactor hu i
  have hInt : ∀ j : Fin n,
      Integrable (fun x =>
        fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) * ψ x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro j
    exact
      ((((hA j).continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
        hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  calc
    ∑ j, ∫ x, (hessianMatrix u x).adjugate i j * fderiv ℝ ψ x (e j) =
        ∑ j, -(∫ x,
          fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) * ψ x) := by
      apply Finset.sum_congr rfl
      intro j _
      exact n10_integration_by_parts (hA j) hψ hψc (e j)
    _ = -(∑ j, ∫ x,
        fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) * ψ x) :=
      Finset.sum_neg_distrib _
    _ = -(∫ x, ∑ j,
        fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) * ψ x) := by
      congr 1
      exact (integral_finsetSum Finset.univ (fun j _ => hInt j)).symm
    _ = 0 := by
      have hz : ∀ x, (∑ j,
          fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) * ψ x) = 0 := by
        intro x
        rw [← Finset.sum_mul]
        change
          (∑ j, fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x
            (EuclideanSpace.basisFun (Fin n) ℝ j)) * ψ x = 0
        rw [sum_fderiv_adjugate_hessianMatrix_eq_zero_408915f hu x i, zero_mul]
      simp only [hz, integral_zero, neg_zero]
/-- Dominated convergence for smooth potentials with a fixed Lipschitz test. -/
private lemma FunctionalInequalities.Analysis.n10_integral_convergence {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {Uk : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hLip : ∀ k, LipschitzWith G (gradient (Uk k)))
    (hconv : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun k => fderiv ℝ (gradient (Uk k)) x) atTop
        (𝓝 (fderiv ℝ (gradient u) x)))
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hψ : LipschitzWith L ψ) (hψc : HasCompactSupport ψ) (i j : Fin n) :
    Tendsto
      (fun k => ∫ x, (hessianMatrix (Uk k) x).adjugate i j *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
      atTop
      (𝓝 (∫ x, (hessianMatrix u x).adjugate i j *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))) := by
  let v := EuclideanSpace.basisFun (Fin n) ℝ j
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (G : ℝ)).exists_bound_of_continuousOn
        (n10_continuous_cofactor i j).continuousOn
  have hb : ∀ k x, ‖(hessianMatrix (Uk k) x).adjugate i j‖ ≤ C := by
    intro k x
    rw [n10_hessian]
    apply hC
    change dist (fderiv ℝ (gradient (Uk k)) x) 0 ≤ (G : ℝ)
    rw [dist_zero_right]
    exact norm_fderiv_le_of_lipschitz ℝ (hLip k)
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => C * ‖fderiv ℝ ψ x v‖)
  · exact Eventually.of_forall fun k =>
      ((n10_measurable_cofactor (Uk k) i j).mul
        (n10_measurable_deriv ψ v)).aestronglyMeasurable
  · exact Eventually.of_forall fun k => Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb k x) (norm_nonneg _)
  · exact (n10_integrable_deriv hψ hψc v).norm.const_mul C
  · filter_upwards [hconv] with x hx
    have ht :=
      ((n10_continuous_cofactor i j).continuousAt.tendsto.comp hx).mul_const
        (fderiv ℝ ψ x v)
    simpa only [n10_hessian, Function.comp_def] using ht
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Weak Piola identity with Lipschitz tests** (weak Letwin route): for `u ∈ C¹` with Lipschitz
gradient and a Lipschitz `ψ` with compact support (`fderiv ℝ ψ` its a.e. derivative),
`∑ⱼ ∫ (adj ∇²u)ᵢⱼ ∂ⱼψ = 0`. -/
theorem solution {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {Lψ : NNReal}
    (hψ : LipschitzWith Lψ ψ) (hψc : HasCompactSupport ψ) (i : Fin n) :
    ∑ j, ∫ x, (FunctionalInequalities.Probability.Stein.hessianMatrix u x).adjugate i j * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 0 := by
  classical
  obtain ⟨Uk, hUk, _, hLip, _, hconv⟩ :=
    FunctionalInequalities.Analysis.exists_contDiff_approx_of_lipschitz_gradient_408915f hu hG
  have hUk₃ : ∀ k, ContDiff ℝ 3 (Uk k) :=
    fun k => (hUk k).of_le
      (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
  have hsum := tendsto_finsetSum Finset.univ
    (fun j _ => n10_integral_convergence hLip hconv hψ hψc i j)
  have hzero : ∀ k,
      (∑ j, ∫ x, (FunctionalInequalities.Probability.Stein.hessianMatrix (Uk k) x).adjugate i j *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j)) = 0 :=
    fun k => n10_smooth_piola (hUk₃ k) hψ hψc i
  have hsumzero : Tendsto
      (fun k => ∑ j, ∫ x, (FunctionalInequalities.Probability.Stein.hessianMatrix (Uk k) x).adjugate i j *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
      atTop (𝓝 0) := by
    simp only [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hsum hsumzero
