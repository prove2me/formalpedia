-- Prove2me | solution 1 for FunctionalInequalities.Analysis.sum_integral_inv_hessianMatrix_mul_fderiv_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:08:54.066146+00:00
-- url     : https://prove2.me/submissions/89ffdafb-f035-48ba-9134-946f72de0759

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
import Theorems.Thm_FunctionalInequalities_Analysis_sum_integral_adjugate_hessianMatrix_mul_fderiv_eq_zero_of_lipschitz_408915f

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
private lemma FunctionalInequalities.Analysis.n10_integrable_weighted_deriv
    {f w : E → ℝ} {L : NNReal} (hf : LipschitzWith L f)
    (hc : HasCompactSupport f) (hw : Continuous w) (v : E) :
    Integrable (fun x => w x * fderiv ℝ f x v) (volume : Measure E) := by
  have hd : LocallyIntegrable (fun x => fderiv ℝ f x v) (volume : Measure E) :=
    (memLp_top_of_bound (n10_measurable_deriv f v).aestronglyMeasurable
      ((L : ℝ) * ‖v‖)
      (Eventually.of_forall (n10_deriv_bound hf v))).locallyIntegrable le_top
  have hl := LocallyIntegrable.continuous_mul hw hd
  apply (hl.integrableOn_isCompact hc.isCompact).integrable_of_forall_notMem_eq_zero
  intro x hx
  rw [n10_deriv_zero hx v, mul_zero]
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
private lemma FunctionalInequalities.Analysis.n10_cofactor_bound {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n) :
    ∃ C : ℝ, ∀ x, ‖(hessianMatrix u x).adjugate i j‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (G : ℝ)).exists_bound_of_continuousOn
        (n10_continuous_cofactor i j).continuousOn
  refine ⟨C, fun x => ?_⟩
  rw [n10_hessian]
  apply hC
  change dist (fderiv ℝ (gradient u) x) 0 ≤ (G : ℝ)
  rw [dist_zero_right]
  exact norm_fderiv_le_of_lipschitz ℝ hG
private lemma FunctionalInequalities.Analysis.n10_lipschitz_product
    {f g : E → ℝ} {Lf Lg : NNReal}
    (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hgb : ∃ D : ℝ, ∀ x, ‖g x‖ ≤ D) :
    ∃ L : NNReal, LipschitzWith L (fun x => f x * g x) := by
  obtain ⟨C, hC⟩ := hfb
  obtain ⟨D, hD⟩ := hgb
  let L : NNReal :=
    ⟨max C 0 * (Lg : ℝ) + max D 0 * (Lf : ℝ), by positivity⟩
  refine ⟨L, lipschitzWith_iff_norm_sub_le.mpr ?_⟩
  intro x y
  calc
    ‖f x * g x - f y * g y‖ =
        ‖f x * (g x - g y) + (f x - f y) * g y‖ := by
      congr 1
      ring
    _ ≤ ‖f x * (g x - g y)‖ + ‖(f x - f y) * g y‖ := norm_add_le _ _
    _ = ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ max C 0 * ((Lg : ℝ) * ‖x - y‖) +
        ((Lf : ℝ) * ‖x - y‖) * max D 0 := by
      apply add_le_add
      · exact mul_le_mul ((hC x).trans (le_max_left _ _))
          (hg.norm_sub_le x y) (norm_nonneg _) (le_max_right _ _)
      · exact mul_le_mul (hf.norm_sub_le x y)
          ((hD y).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
    _ = (L : ℝ) * ‖x - y‖ := by
      change max C 0 * ((Lg : ℝ) * ‖x - y‖) +
        ((Lf : ℝ) * ‖x - y‖) * max D 0 =
          (max C 0 * (Lg : ℝ) + max D 0 * (Lf : ℝ)) * ‖x - y‖
      ring
end StructuredSpace
private lemma FunctionalInequalities.Analysis.n10_exp_test_lipschitz {n : ℕ}
    {F ψ : EuclideanSpace ℝ (Fin n) → ℝ} {LF Lψ : NNReal}
    (hF : LipschitzWith LF F) (hψ : LipschitzWith Lψ ψ)
    (hψc : HasCompactSupport ψ) :
    ∃ L : NNReal, LipschitzWith L (fun x => Real.exp (-F x) * ψ x) := by
  obtain ⟨χ, hχ, hχc, hχeq⟩ :=
    n10_cutoff (hψc.isCompact.image hF.continuous)
  let q : ℝ → ℝ := fun t => χ t * Real.exp (-t)
  have hq : ContDiff ℝ 1 q := hχ.mul contDiff_id.neg.exp
  have hqc : HasCompactSupport q := hχc.mul_right
  obtain ⟨Lq, hLq⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hqc hq one_ne_zero
  obtain ⟨C, hC⟩ := hqc.exists_bound_of_continuous hq.continuous
  obtain ⟨L, hL⟩ := n10_lipschitz_product (hLq.comp hF) hψ
    ⟨C, fun x => hC (F x)⟩
    (hψc.exists_bound_of_continuous hψ.continuous)
  have he :
      (fun x => q (F x) * ψ x) =
        (fun x => Real.exp (-F x) * ψ x) := by
    funext x
    by_cases hx : x ∈ tsupport ψ
    · have hh := (hχeq (F x) (mem_image_of_mem F hx)).eq_of_nhds
      change (χ (F x) * Real.exp (-F x)) * ψ x = _
      rw [hh, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
  refine ⟨L, ?_⟩
  change LipschitzWith L (fun x => q (F x) * ψ x) at hL
  rw [he] at hL
  exact hL
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Divergence of the inverse Hessian** (weak Letwin route): if moreover `det ∇²u = e^F` a.e. for a
Lipschitz `F`, then for Lipschitz `ψ` with compact support
`∑ⱼ ∫ (∇²u)⁻¹ᵢⱼ ∂ⱼψ = ∑ⱼ ∫ (∇²u)⁻¹ᵢⱼ ∂ⱼF ψ`, i.e. `div (∇²u)⁻¹ = −(∇²u)⁻¹ ∇F` weakly. -/
theorem solution {n : ℕ}
    {u F : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) {LF : NNReal} (hF : LipschitzWith LF F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (F x))
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {Lψ : NNReal} (hψ : LipschitzWith Lψ ψ)
    (hψc : HasCompactSupport ψ) (i : Fin n) :
    ∑ j, ∫ x, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      ∑ j, ∫ x, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ j) * ψ x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hw : Continuous (fun x => Real.exp (-F x)) :=
    Real.continuous_exp.comp hF.continuous.neg
  have htc : HasCompactSupport (fun x => Real.exp (-F x) * ψ x) :=
    hψc.mul_left
  obtain ⟨Lt, ht⟩ := n10_exp_test_lipschitz hF hψ hψc
  have hzero :=
    FunctionalInequalities.Analysis.sum_integral_adjugate_hessianMatrix_mul_fderiv_eq_zero_of_lipschitz_408915f
      hu hG ht htc i
  have hinv :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ∀ r s, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ r s =
          Real.exp (-F x) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x).adjugate r s := by
    filter_upwards [hdet] with x hx
    intro r s
    simp only [Matrix.inv_def, hx, Ring.inverse_eq_inv, Matrix.smul_apply,
      smul_eq_mul, Real.exp_neg]
  have hd :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ∀ v, fderiv ℝ (fun y => Real.exp (-F y) * ψ y) x v =
          Real.exp (-F x) * (fderiv ℝ ψ x v - ψ x * fderiv ℝ F x v) := by
    filter_upwards [hF.ae_differentiableAt
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))),
      hψ.ae_differentiableAt
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))] with x hx hy
    have he :
        fderiv ℝ (fun y => Real.exp (-F y) * ψ y) x =
          Real.exp (-F x) • fderiv ℝ ψ x +
            ψ x • (Real.exp (-F x) • (-fderiv ℝ F x)) :=
      ((hx.hasFDerivAt.neg.exp).mul hy.hasFDerivAt).fderiv
    intro v
    rw [he]
    simp only [_root_.add_apply, _root_.smul_apply, _root_.neg_apply, smul_eq_mul]
    ring
  have hA : ∀ j : Fin n,
      Integrable (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * fderiv ℝ ψ x (e j))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro j
    obtain ⟨C, hC⟩ := n10_cofactor_bound hG i j
    have hi := (n10_integrable_weighted_deriv hψ hψc hw (e j)).bdd_mul
      (n10_measurable_cofactor u i j).aestronglyMeasurable
      (Eventually.of_forall hC)
    apply hi.congr
    filter_upwards [hinv] with x hx
    change (FunctionalInequalities.Probability.Stein.hessianMatrix u x).adjugate i j *
        (Real.exp (-F x) * fderiv ℝ ψ x (e j)) =
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * fderiv ℝ ψ x (e j)
    rw [hx i j]
    ring
  have hB : ∀ j : Fin n,
      Integrable (fun x =>
        (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * fderiv ℝ F x (e j) * ψ x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro j
    obtain ⟨C, hC⟩ := n10_cofactor_bound hG i j
    have hi :=
      (hw.mul hψ.continuous).integrable_of_hasCompactSupport
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) htc
    have hi' := hi.bdd_mul (n10_measurable_deriv F (e j)).aestronglyMeasurable
      (Eventually.of_forall (n10_deriv_bound hF (e j)))
    have hi'' := hi'.bdd_mul (n10_measurable_cofactor u i j).aestronglyMeasurable
      (Eventually.of_forall hC)
    apply hi''.congr
    filter_upwards [hinv] with x hx
    change (FunctionalInequalities.Probability.Stein.hessianMatrix u x).adjugate i j *
        (fderiv ℝ F x (e j) * (Real.exp (-F x) * ψ x)) =
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * fderiv ℝ F x (e j) * ψ x
    rw [hx i j]
    ring
  have hsplit (j : Fin n) :
      (∫ x, (FunctionalInequalities.Probability.Stein.hessianMatrix u x).adjugate i j *
        fderiv ℝ (fun y => Real.exp (-F y) * ψ y) x (e j)) =
      (∫ x, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * fderiv ℝ ψ x (e j)) -
      (∫ x, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * fderiv ℝ F x (e j) * ψ x) := by
    calc
      (∫ x, (FunctionalInequalities.Probability.Stein.hessianMatrix u x).adjugate i j *
          fderiv ℝ (fun y => Real.exp (-F y) * ψ y) x (e j)) =
          ∫ x, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * fderiv ℝ ψ x (e j) -
            (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * fderiv ℝ F x (e j) * ψ x := by
        apply integral_congr_ae
        filter_upwards [hinv, hd] with x hx hxD
        rw [hxD (e j), hx i j]
        ring
      _ = _ := integral_sub (hA j) (hB j)
  change (∑ j, ∫ x, (FunctionalInequalities.Probability.Stein.hessianMatrix u x).adjugate i j *
    fderiv ℝ (fun y => Real.exp (-F y) * ψ y) x (e j)) = 0 at hzero
  simp only [hsplit, Finset.sum_sub_distrib] at hzero
  exact sub_eq_zero.mp hzero
