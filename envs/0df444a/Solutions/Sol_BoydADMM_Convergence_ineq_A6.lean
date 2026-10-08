-- Prove2me | solution 1 for BoydADMM.Convergence.ineq_A6
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:29:37.01044+00:00
-- url     : https://prove2.me/submissions/2c830d08-a934-4777-bd29-a3107da74361

import Definitions.Def_BoydADMM_Convergence_Model
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential
import Theorems.Thm_BoydADMM_Convergence_ineq_A2
import Theorems.Thm_BoydADMM_Convergence_ineq_A3
open Filter
open scoped Topology
namespace BoydADMM.Convergence

private lemma norm_affine_sq {a : ℕ} (r d : EuclideanSpace ℝ (Fin a)) (t : ℝ) :
    ‖r + t • d‖ ^ 2 = ‖r‖ ^ 2 + 2 * t * inner ℝ r d + t ^ 2 * ‖d‖ ^ 2 := by
  simp [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, real_inner_smul_right]
  ring


end BoydADMM.Convergence
open BoydADMM.Convergence
/-- (A.6), p. 110: `V^k − V^{k+1} ≥ ρ‖r^{k+1} − B(z^{k+1} − z^k)‖₂²` for every `k ≥ 0`,
with `V^k = (1/ρ)‖y^k − y⋆‖₂² + ρ‖B(z^k − z⋆)‖₂²`. -/
theorem solution
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) (k : ℕ) :
    P.lyapunov ρ zs ys (z k) (y k) - P.lyapunov ρ zs ys (z (k + 1)) (y (k + 1)) ≥
      ρ * ‖P.resid (x (k + 1)) (z (k + 1)) - P.Bmul (z (k + 1) - z k)‖ ^ 2 := by
  have h2 := ineq_A2 P hA1 hρ hsp hrun k
  have h3 := ineq_A3 P hA1 hρ hsp hrun k
  let r := P.resid (x (k+1)) (z (k+1))
  let d := P.Bmul (z (k+1)-z k)
  let u := y k - ys
  let v := P.Bmul (z k-zs)
  have hy : y (k+1)-ys = u+ρ • r := by
    dsimp [u,r]
    rw [hrun.y_succ k]
    abel
  have hz : P.Bmul (z (k+1)-zs) = v+d := by
    dsimp [v,d,Problem.Bmul]
    rw [← map_add]
    congr 1
    abel
  have hh : inner ℝ (u+ρ • r) r - ρ * inner ℝ d r +
      ρ * inner ℝ d (v+d) ≤ 0 := by
    rw [← hy, ← hz]
    simp only [inner_sub_left, inner_add_right, inner_neg_right] at *
    dsimp [r,d]
    linarith
  have hid : (1/ρ)*‖u‖^2+ρ*‖v‖^2 - ((1/ρ)*‖u+ρ • r‖^2+ρ*‖v+d‖^2) -
      ρ*‖r-d‖^2 = -2*(inner ℝ (u+ρ • r) r - ρ*inner ℝ d r + ρ*inner ℝ d (v+d)) := by
    rw [norm_affine_sq u r ρ, norm_add_sq_real v d, norm_sub_sq_real r d]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [real_inner_comm d r, real_inner_comm d v]
    field_simp [ne_of_gt hρ]
    ring
  change (1/ρ)*‖y k-ys‖^2+ρ*‖P.Bmul (z k-zs)‖^2 -
    ((1/ρ)*‖y (k+1)-ys‖^2+ρ*‖P.Bmul (z (k+1)-zs)‖^2) ≥ ρ*‖r-d‖^2
  rw [hy,hz]
  change (1/ρ)*‖u‖^2+ρ*‖v‖^2 - ((1/ρ)*‖u+ρ • r‖^2+ρ*‖v+d‖^2) ≥ ρ*‖r-d‖^2
  linarith


