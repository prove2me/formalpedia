-- Prove2me | solution 1 for FunctionalInequalities.Analysis.smooth_test_derivative_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:33:30.67369+00:00
-- url     : https://prove2.me/submissions/efd14218-8f96-4f03-9cc8-69001742c526

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak

noncomputable section
section GeneratorIdentities
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
 lemma solution {n : ℕ}
    {u a f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (ha : ContDiff ℝ 1 a)
    (hf : ContDiff ℝ 2 f) (i j : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    FunctionalInequalities.Analysis.coord (FunctionalInequalities.Analysis.weightedTest u a f i) j x =
      Real.exp (-u x) *
        (FunctionalInequalities.Analysis.coord a j x * FunctionalInequalities.Analysis.coord f i x -
          a x * FunctionalInequalities.Analysis.coord u j x * FunctionalInequalities.Analysis.coord f i x +
          a x * FunctionalInequalities.Probability.Stein.hessianMatrix f x j i) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num)
  have hfdx := (hfd.differentiable one_ne_zero).differentiableAt (x := x)
  have hc :
      DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ i) x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ i) :
      Differentiable ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ i)).differentiableAt
  have hcomponent : DifferentiableAt ℝ (FunctionalInequalities.Analysis.coord f i) x :=
    hfdx.clm_apply hc
  have hcoord :
      FunctionalInequalities.Analysis.coord (FunctionalInequalities.Analysis.coord f i) j x = FunctionalInequalities.Probability.Stein.hessianMatrix f x j i := by
    have he := congrArg
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        L (EuclideanSpace.basisFun (Fin n) ℝ j))
      (fderiv_clm_apply hfdx hc)
    change
      fderiv ℝ
        (fun y => fderiv ℝ f y (EuclideanSpace.basisFun (Fin n) ℝ i)) x
        (EuclideanSpace.basisFun (Fin n) ℝ j) =
          FunctionalInequalities.Probability.Stein.hessianMatrix f x j i
    simpa [FunctionalInequalities.Probability.Stein.hessianMatrix, bilinearIteratedFDerivTwo] using he
  have hux : DifferentiableAt ℝ u x :=
    hu.differentiable one_ne_zero x
  have hax : DifferentiableAt ℝ a x :=
    ha.differentiable one_ne_zero x
  have he :
      fderiv ℝ (FunctionalInequalities.Analysis.weightedTest u a f i) x =
        (a x * Real.exp (-u x)) • fderiv ℝ (FunctionalInequalities.Analysis.coord f i) x +
          FunctionalInequalities.Analysis.coord f i x •
            (a x • (Real.exp (-u x) • (-fderiv ℝ u x)) +
              Real.exp (-u x) • fderiv ℝ a x) :=
    ((hax.hasFDerivAt.mul hux.hasFDerivAt.neg.exp).mul
      hcomponent.hasFDerivAt).fderiv
  change fderiv ℝ (FunctionalInequalities.Analysis.weightedTest u a f i) x
    (EuclideanSpace.basisFun (Fin n) ℝ j) = _
  rw [he]
  simp only [_root_.add_apply, _root_.smul_apply, _root_.neg_apply, smul_eq_mul]
  change
    (a x * Real.exp (-u x)) * FunctionalInequalities.Analysis.coord (FunctionalInequalities.Analysis.coord f i) j x +
      FunctionalInequalities.Analysis.coord f i x *
        (a x * (Real.exp (-u x) * (-FunctionalInequalities.Analysis.coord u j x)) +
          Real.exp (-u x) * FunctionalInequalities.Analysis.coord a j x) = _
  rw [hcoord]
  ring
