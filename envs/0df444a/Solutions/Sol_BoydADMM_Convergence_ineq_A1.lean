-- Prove2me | solution 1 for BoydADMM.Convergence.ineq_A1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:31:33.77385+00:00
-- url     : https://prove2.me/submissions/25974d35-194e-4af8-a612-8628da123373

import Definitions.Def_BoydADMM_Convergence_Model
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential
import Theorems.Thm_BoydADMM_Convergence_ineq_A6
import Theorems.Thm_BoydADMM_Convergence_dual_step_monotone
open Filter
open scoped Topology
namespace BoydADMM.Convergence


end BoydADMM.Convergence
open BoydADMM.Convergence
/-- (A.1), p. 107: `V^{k+1} ≤ V^k − ρ‖r^{k+1}‖₂² − ρ‖B(z^{k+1} − z^k)‖₂²` for every book
index `k ≥ 1` (here written with `k + 1` in place of the book's `k`). -/
theorem solution
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) (k : ℕ) :
    P.lyapunov ρ zs ys (z (k + 2)) (y (k + 2)) ≤
      P.lyapunov ρ zs ys (z (k + 1)) (y (k + 1))
        - ρ * ‖P.resid (x (k + 2)) (z (k + 2))‖ ^ 2
        - ρ * ‖P.Bmul (z (k + 2) - z (k + 1))‖ ^ 2 := by
  have h6 := ineq_A6 P hA1 hρ hsp hrun (k+1)
  have hm := dual_step_monotone P hA1 hρ hrun k
  have hy : y (k+2)-y (k+1) = ρ • P.resid (x (k+2)) (z (k+2)) := by
    rw [hrun.y_succ (k+1)]
    abel
  rw [hy, real_inner_smul_left] at hm
  rw [norm_sub_sq_real] at h6
  change P.lyapunov ρ zs ys (z (k+1)) (y (k+1)) -
    P.lyapunov ρ zs ys (z (k+2)) (y (k+2)) ≥
    ρ * (‖P.resid (x (k+2)) (z (k+2))‖^2 -
    2*inner ℝ (P.resid (x (k+2)) (z (k+2))) (P.Bmul (z (k+2)-z (k+1))) +
    ‖P.Bmul (z (k+2)-z (k+1))‖^2) at h6
  nlinarith


