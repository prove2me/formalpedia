-- Prove2me | solution 1 for EpOpEvalPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:54:06.802797+00:00
-- url     : https://prove2.me/submissions/dc700759-7e5f-4ecb-84d0-2926a137b41e

module
public import Definitions.Def_PHarmonicPoly_EpAlg
public import Definitions.Def_PHarmonicPoly_EpOp
public import Definitions.Def_PHarmonicPoly_MvPolyLaplacian
public import Definitions.Def_PHarmonicPoly_EpOpEvalPoly
public import Theorems.Thm_MvPolyGradient
public import Theorems.Thm_MvPolyHessian
public import Theorems.Thm_MvPolyLaplacian


set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {n : ℕ} (p : ℝ) (P : MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    EpOp p (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x
      = MvPolynomial.eval (fun i => x i) (EpAlg p P) := by
  have hg : ∀ i : Fin n,
      gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun j => y j) P) x i
        = MvPolynomial.eval (fun j => x j) (pderiv i P) := by
    intro i; rw [MvPolyGradient P x]
  have hA : ‖gradient (fun y : EuclideanSpace ℝ (Fin n) =>
        MvPolynomial.eval (fun j => y j) P) x‖ ^ 2
      = ∑ i, (MvPolynomial.eval (fun j => x j) (pderiv i P)) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h := hg i
    simp only [RCLike.inner_apply, conj_trivial, sq]
    rw [show (gradient (fun y : EuclideanSpace ℝ (Fin n) =>
        MvPolynomial.eval (fun j => y j) P) x).ofLp i
      = MvPolynomial.eval (fun j => x j) (pderiv i P) from h]
  have hC : iteratedFDeriv ℝ 2
        (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun j => y j) P) x
        ![gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun j => y j) P) x,
          gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun j => y j) P) x]
      = ∑ i, ∑ j, MvPolynomial.eval (fun k => x k) (pderiv i (pderiv j P))
          * MvPolynomial.eval (fun k => x k) (pderiv i P)
          * MvPolynomial.eval (fun k => x k) (pderiv j P) := by
    rw [MvPolyHessian P x _ _]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
      rw [hg i, hg j]; ring))
  rw [EpOp, hA, MvPolyLaplacian P x, hC, EpAlg]
  simp only [map_add, map_mul, map_sum, map_pow, eval_C]
