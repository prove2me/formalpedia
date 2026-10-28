-- Prove2me | solution 1 for FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:32.203489+00:00
-- url     : https://prove2.me/submissions/1912ce50-9ad2-45cd-9554-299fc379ca66

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak

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
/-- The coordinate Hessian of a `C¹` potential is symmetric at every differentiability
point of its gradient, including the zero-dimensional case. -/
theorem FunctionalInequalities.Probability.Stein.hessianMatrix_isHermitian_of_differentiableAt_gradient
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x) :
    (hessianMatrix u x).IsHermitian := by
  change (hessianMatrix u x).conjTranspose = hessianMatrix u x
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  exact hessian_symm_of_gradient_diff hu hx
end
end GradientDerivativeIdentification
end

noncomputable section
section MongeAmpereExponentDerivative
open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace ContDiff
private lemma FunctionalInequalities.Analysis.gradient_fderiv_coordinate {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x)
    (j k : Fin n) :
    fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k =
      hessianMatrix u x j k := by
  have hm :
      LinearMap.toMatrix
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
          (fderiv ℝ (gradient u) x).toLinearMap =
        hessianMatrix u x := by
    rw [← hessianMatrix_toEuclideanLin_of_differentiableAt_gradient hu hx,
      Matrix.toEuclideanLin_eq_toLin_orthonormal,
      LinearMap.toMatrix_toLin]
  have hentry :
      fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k =
        hessianMatrix u x k j := by
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M k j) hm
    simp only [LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, OrthonormalBasis.coe_toBasis] at he
    exact he
  calc
    fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k =
        hessianMatrix u x k j := hentry
    _ = hessianMatrix u x j k := by
      simpa only [star_trivial] using
        (hessianMatrix_isHermitian_of_differentiableAt_gradient hu hx).apply j k
/-- AE coordinate chain derivative of the Monge-Ampere right-hand exponent
for Letwin (2.2), with C1 u and Lipschitz gradient, without a C2 premise. -/
theorem solution {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j : Fin n,
      fderiv ℝ (fun y => -u y + V (gradient u y)) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) =
        -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
          ∑ k, FunctionalInequalities.Probability.Stein.hessianMatrix u x j k *
            fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
  filter_upwards [hG.ae_differentiableAt (μ := volume)] with x hx
  intro j
  have hux : DifferentiableAt ℝ u x := hu.differentiable one_ne_zero x
  have hVx : DifferentiableAt ℝ V (gradient u x) :=
    hV.differentiable one_ne_zero (gradient u x)
  have hexp :
      HasFDerivAt (fun y => -u y + V (gradient u y))
        (-fderiv ℝ u x +
          (fderiv ℝ V (gradient u x)).comp (fderiv ℝ (gradient u) x)) x :=
    hux.hasFDerivAt.neg.add (hVx.hasFDerivAt.comp x hx.hasFDerivAt)
  have heval :
      fderiv ℝ (fun y => -u y + V (gradient u y)) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) =
        -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
          fderiv ℝ V (gradient u x)
            (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
    exact congrArg
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        L (EuclideanSpace.basisFun (Fin n) ℝ j))
      hexp.fderiv
  have hchain :
      fderiv ℝ V (gradient u x)
          (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j)) =
        ∑ k, FunctionalInequalities.Probability.Stein.hessianMatrix u x j k *
          fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
    calc
      fderiv ℝ V (gradient u x)
          (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j)) =
          ⟪gradient V (gradient u x),
            fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ :=
        inner_gradient_left.symm
      _ = ∑ k, ⟪gradient V (gradient u x) k,
          fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k⟫ :=
        PiLp.inner_apply _ _
      _ = ∑ k, FunctionalInequalities.Probability.Stein.hessianMatrix u x j k *
          fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
        apply Finset.sum_congr rfl
        intro k _
        have hVk :
            fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) =
              gradient V (gradient u x) k := by
          calc
            fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) =
                ⟪gradient V (gradient u x),
                  EuclideanSpace.basisFun (Fin n) ℝ k⟫ :=
              inner_gradient_left.symm
            _ = gradient V (gradient u x) k :=
              EuclideanSpace.inner_basisFun_real
                (Fin n) (gradient V (gradient u x)) k
        calc
          ⟪gradient V (gradient u x) k,
              fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k⟫ =
              gradient V (gradient u x) k *
                fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k :=
            Real.inner_apply _ _
          _ = gradient V (gradient u x) k * FunctionalInequalities.Probability.Stein.hessianMatrix u x j k :=
            congrArg (fun t : ℝ => gradient V (gradient u x) k * t)
              (FunctionalInequalities.Analysis.gradient_fderiv_coordinate hu hx j k)
          _ = FunctionalInequalities.Probability.Stein.hessianMatrix u x j k * gradient V (gradient u x) k :=
            mul_comm _ _
          _ = FunctionalInequalities.Probability.Stein.hessianMatrix u x j k *
              fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) :=
            congrArg (fun t : ℝ => FunctionalInequalities.Probability.Stein.hessianMatrix u x j k * t) hVk.symm
  exact heval.trans
    (congrArg
      (fun t : ℝ => -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) + t)
      hchain)
