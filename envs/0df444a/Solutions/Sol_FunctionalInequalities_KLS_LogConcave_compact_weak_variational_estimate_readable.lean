-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.compact_weak_variational_estimate_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:39:12.322293+00:00
-- url     : https://prove2.me/submissions/bfe156f1-d0a2-405e-8a1f-31a6c454b443

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeakBrascampLieb
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_compact_ordinary_diffusion_coercivity_of_lipschitz_gradient_readable
import Theorems.Thm_FunctionalInequalities_Analysis_integral_bounded_weak_mul_weightedLaplacian_of_contDiff_one_readable
import Theorems.Thm_FunctionalInequalities_Analysis_inverse_quadratic_young_readable

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section WeakThirdDerivativeSymmetry
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Stein
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section InnerProduct
variable [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.differentiableAt_fderiv_of_differentiableAt_gradient [CompleteSpace E]
    {u : E → ℝ} {x : E} (hx : DifferentiableAt ℝ (gradient u) x) :
    DifferentiableAt ℝ (fderiv ℝ u) x := by
  have heq :
      fderiv ℝ u = (InnerProductSpace.toDual ℝ E) ∘ gradient u := by
    funext y
    simp [gradient]
  rw [heq]
  exact
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.differentiableAt.comp x hx
private lemma FunctionalInequalities.Analysis.hessian_coord_of_gradient_diff
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {i j : Fin n} (hx : DifferentiableAt ℝ (gradient u) x) :
    fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ j)) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) =
      hessianMatrix u x i j := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hc :
      DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j) x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ j) :
      Differentiable ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j)).differentiableAt
  have h := fderiv_clm_apply hfd hc
  have h' := congrArg
    (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin n) ℝ i)) h
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using h'
private lemma FunctionalInequalities.Analysis.hessian_symm_of_gradient_diff
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {i j : Fin n} (hu : ContDiff ℝ 1 u)
    (hx : DifferentiableAt ℝ (gradient u) x) :
    hessianMatrix u x i j = hessianMatrix u x j i := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hs :=
    second_derivative_symmetric
      (fun y => (hu.differentiable (by simp) y).hasFDerivAt)
      hfd.hasFDerivAt
      (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using hs
end InnerProduct
end StructuredSpace
end WeakThirdDerivativeSymmetry
section GradientDerivativeIdentification
open FunctionalInequalities.Analysis
section
private lemma FunctionalInequalities.Probability.Stein.hessianMatrix_entry_of_differentiableAt_gradient
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x) (i j : Fin n) :
    hessianMatrix u x i j =
      ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ := by
  rw [hessian_symm_of_gradient_diff hu hx,
    ← hessian_coord_of_gradient_diff hx]
  have heq :
      (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ i)) =
        fun y => ⟪gradient u y, EuclideanSpace.basisFun (Fin n) ℝ i⟫ := by
    funext y
    exact inner_gradient_left.symm
  rw [heq, fderiv_inner_apply ℝ hx
    (differentiableAt_const (EuclideanSpace.basisFun (Fin n) ℝ i))]
  simp [real_inner_comm]
/-- At a point where the gradient of a `C¹` potential is differentiable, its derivative
is represented by the coordinate Hessian. This pointwise bridge requires no `C²` hypothesis
and supports the weak regular moment-potential package for Letwin's Lemma 2.2. -/
theorem FunctionalInequalities.Probability.Stein.hessianMatrix_toEuclideanLin_of_differentiableAt_gradient
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x) :
    Matrix.toEuclideanLin (hessianMatrix u x) =
      (fderiv ℝ (gradient u) x).toLinearMap := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
  rw [LinearMap.toMatrix_toLin]
  ext i j
  rw [LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]
  exact hessianMatrix_entry_of_differentiableAt_gradient hu hx i j
end
end GradientDerivativeIdentification
end

noncomputable section
open MeasureTheory Filter Topology Set InnerProductSpace Matrix
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open scoped ContDiff RealInnerProductSpace
private theorem FunctionalInequalities.KLS.LogConcave.hessian_pairing_eq_coordinate_quadratic {n : ℕ}
    {U : EuclideanSpace ℝ (Fin n) → ℝ} (hU : ContDiff ℝ 1 U)
    {x : EuclideanSpace ℝ (Fin n)} (hx : DifferentiableAt ℝ (gradient U) x)
    (v : EuclideanSpace ℝ (Fin n)) :
    ⟪fderiv ℝ (gradient U) x v, v⟫ =
      (fun i => v i) ⬝ᵥ (hessianMatrix U x *ᵥ (fun i => v i)) := by
  have he := congrArg (fun A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n) => A v)
    (hessianMatrix_toEuclideanLin_of_differentiableAt_gradient hU hx)
  change Matrix.toEuclideanLin (hessianMatrix U x) v = fderiv ℝ (gradient U) x v at he
  rw [← he, EuclideanSpace.inner_eq_star_dotProduct]
  change (fun i => v i) ⬝ᵥ star (hessianMatrix U x *ᵥ (fun i => v i)) = _
  simp only [star_trivial]
set_option maxHeartbeats 2000000 in
/-- Weak compact variational estimate: the C1,1 sibling of `compact_variational_estimate` for a globally bounded
locally integrable weak test with compact-local L2 coordinate derivatives and finite inverse-Hessian energy. -/
theorem solution {n : ℕ}
    {nu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    {U eta v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hnuU : (nu : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))
    (hU : ContDiff ℝ 1 U) {G : NNReal} (hG : LipschitzWith G (gradient U))
    {L : NNReal} (hL : LipschitzWith L U)
    (hnorm : (∫ x, Real.exp (-U x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (FunctionalInequalities.Probability.Stein.hessianMatrix U x).PosDef)
    (a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ)
    (heta : LocallyIntegrable eta (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖eta x‖ ≤ C)
    (hweak : ∀ i : Fin n, FunctionalInequalities.Analysis.HasWeakDerivAlong eta (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (henergy : Integrable (fun x => (fun i => a i x) ⬝ᵥ
      ((FunctionalInequalities.Probability.Stein.hessianMatrix U x)⁻¹ *ᵥ (fun i => a i x))) (nu : Measure (EuclideanSpace ℝ (Fin n))))
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    Integrable (fun x => eta x * (-FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U v x)) (nu : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U v x ^ 2) (nu : Measure (EuclideanSpace ℝ (Fin n))) ∧
    2 * (∫ x, eta x * (-FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U v x) ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) -
      (∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U v x ^ 2 ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        ∫ x, (fun i => a i x) ⬝ᵥ ((FunctionalInequalities.Probability.Stein.hessianMatrix U x)⁻¹ *ᵥ (fun i => a i x))
          ∂(nu : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  let dv := fun x i => fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)
  obtain ⟨hpair0, hgrad, hpair⟩ :=
    FunctionalInequalities.Analysis.integral_bounded_weak_mul_weightedLaplacian_of_contDiff_one_readable
      hU hv hvc hnorm a C heta hbound hweak ha2
  rw [← hnuU] at hpair0 hgrad hpair
  have hpairInt : Integrable (fun x => eta x * (-FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U v x))
      (nu : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply hpair0.neg.congr
    exact Filter.Eventually.of_forall fun x => by simp only [Pi.neg_apply, mul_neg]
  have hpair' : (∫ x, eta x * (-FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U v x) ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, (fun i => a i x) ⬝ᵥ dv x ∂(nu : Measure (EuclideanSpace ℝ (Fin n))) := by
    simp only [mul_neg, integral_neg]
    change -(∫ x, eta x * FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U v x ∂(nu : Measure (EuclideanSpace ℝ (Fin n)))) = _
    rw [hpair, neg_neg]
    rfl
  have hexp : Integrable (fun x => Real.exp (-U x)) volume :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  obtain ⟨hQ, hLap, hcoer⟩ :=
    FunctionalInequalities.Analysis.BakryEmery.compact_ordinary_diffusion_coercivity_of_lipschitz_gradient_readable hU hG hL hexp hv hvc
  rw [← hnuU] at hQ hLap hcoer
  have hac : (nu : Measure (EuclideanSpace ℝ (Fin n))) ≪
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [hnuU]
    exact tilted_absolutelyContinuous _ _
  have hEqual : (fun x => ⟪fderiv ℝ (gradient U) x (gradient v x), gradient v x⟫) =ᵐ[
      (nu : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => dv x ⬝ᵥ (FunctionalInequalities.Probability.Stein.hessianMatrix U x *ᵥ dv x)) := by
    filter_upwards [hac.ae_le (hG.ae_differentiableAt (μ := volume))] with x hx
    have hdv : dv x = (fun i => gradient v x i) := by
      funext i
      dsimp only [dv]
      rw [← inner_gradient_left, EuclideanSpace.inner_basisFun_real]
    rw [hdv]
    exact FunctionalInequalities.KLS.LogConcave.hessian_pairing_eq_coordinate_quadratic hU hx (gradient v x)
  have hH := hQ.congr hEqual
  rw [integral_congr_ae hEqual] at hcoer
  have hyoung := integral_mono_ae (hgrad.const_mul 2) (henergy.add hH) (by
    filter_upwards [hac.ae_le hPD] with x hx
    exact FunctionalInequalities.Analysis.inverse_quadratic_young_readable (FunctionalInequalities.Probability.Stein.hessianMatrix U x) hx (fun i => a i x) (dv x))
  simp only [Pi.add_apply] at hyoung
  rw [integral_const_mul, integral_add henergy hH] at hyoung
  refine ⟨hpairInt, hLap, ?_⟩
  rw [hpair']
  dsimp only [dv, dotProduct] at hyoung hcoer ⊢
  linarith only [hyoung, hcoer]
