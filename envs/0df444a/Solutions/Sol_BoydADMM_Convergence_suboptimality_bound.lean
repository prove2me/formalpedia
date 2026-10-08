-- Prove2me | solution 1 for BoydADMM.Convergence.suboptimality_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:31:36.471731+00:00
-- url     : https://prove2.me/submissions/a228f960-89d6-4713-8a13-ab4384a91407

import Definitions.Def_BoydADMM_Convergence_Model
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential
import Theorems.Thm_BoydADMM_Convergence_ineq_3_11
open Filter
open scoped Topology
namespace BoydADMM.Convergence


end BoydADMM.Convergence
open BoydADMM.Convergence
/-- §3.3.1, p. 19: if `‖x^k − x⋆‖₂ ≤ d` then
`f(x^k) + g(z^k) − p⋆ ≤ −(y^k)ᵀr^k + d‖s^k‖₂ ≤ ‖y^k‖₂‖r^k‖₂ + d‖s^k‖₂`, for every `k ≥ 1`
(written as `k + 1`, `k ≥ 0`). -/
theorem solution
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) (k : ℕ) (d : ℝ) (hd : ‖x (k + 1) - xs‖ ≤ d) :
    P.f (x (k + 1)) + P.g (z (k + 1)) - P.optVal ≤
        -inner ℝ (y (k + 1)) (P.resid (x (k + 1)) (z (k + 1)))
          + d * ‖P.dualResid ρ (z k) (z (k + 1))‖ ∧
      -inner ℝ (y (k + 1)) (P.resid (x (k + 1)) (z (k + 1)))
          + d * ‖P.dualResid ρ (z k) (z (k + 1))‖ ≤
        ‖y (k + 1)‖ * ‖P.resid (x (k + 1)) (z (k + 1))‖
          + d * ‖P.dualResid ρ (z k) (z (k + 1))‖ := by
  have h := ineq_3_11 P hA1 hρ hsp hrun k
  have hcs := real_inner_le_norm (x (k+1)-xs) (P.dualResid ρ (z k) (z (k+1)))
  have hmul := mul_le_mul_of_nonneg_right hd (norm_nonneg (P.dualResid ρ (z k) (z (k+1))))
  have hneg := real_inner_le_norm (-(y (k+1))) (P.resid (x (k+1)) (z (k+1)))
  simp only [inner_neg_left,norm_neg] at hneg
  constructor <;> linarith


