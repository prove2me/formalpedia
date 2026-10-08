-- Prove2me | solution 1 for BoydADMM.Convergence.ineq_3_11
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:29:31.818192+00:00
-- url     : https://prove2.me/submissions/8ebe817c-7ee0-4347-8667-299389a24153

import Definitions.Def_BoydADMM_Convergence_Model
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential
import Theorems.Thm_BoydADMM_Convergence_ineq_A2
open Filter
open scoped Topology
namespace BoydADMM.Convergence

private lemma transpose_inner {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ)
    (u : EuclideanSpace ℝ (Fin a)) (v : EuclideanSpace ℝ (Fin b)) :
    inner ℝ (Matrix.toEuclideanLin M.transpose u) v = inner ℝ u (Matrix.toEuclideanLin M v) := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]

private lemma saddle_feasible {n m p : ℕ} (P : Problem n m p)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys) : P.resid xs zs = 0 := by
  have h := hsp.2.2.1 (ys + P.resid xs zs)
  simp only [Problem.augLag, zero_div, zero_mul, add_zero, inner_add_left,
    real_inner_self_eq_norm_sq] at h
  have hn : ‖P.resid xs zs‖ = 0 := by nlinarith [norm_nonneg (P.resid xs zs)]
  exact norm_eq_zero.mp hn


end BoydADMM.Convergence
open BoydADMM.Convergence
/-- (3.11), p. 19 (stated at index `k + 1` on p. 107): for every `k ≥ 0`,
`f(x^{k+1}) + g(z^{k+1}) − p⋆ ≤ −(y^{k+1})ᵀr^{k+1} + (x^{k+1} − x⋆)ᵀs^{k+1}`,
with `s^{k+1} = ρAᵀB(z^{k+1} − z^k)`. -/
theorem solution
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) (k : ℕ) :
    P.f (x (k + 1)) + P.g (z (k + 1)) - P.optVal ≤
      -inner ℝ (y (k + 1)) (P.resid (x (k + 1)) (z (k + 1)))
        + inner ℝ (x (k + 1) - xs) (P.dualResid ρ (z k) (z (k + 1))) := by
  have h := ineq_A2 P hA1 hρ hsp hrun k
  have hc : P.c = P.Amul xs + P.Bmul zs := (sub_eq_zero.mp (saddle_feasible P hsp)).symm
  have he : -P.resid (x (k+1)) (z (k+1)) + P.Bmul (z (k+1)-zs) =
      -P.Amul (x (k+1)-xs) := by
    simp only [Problem.resid, hc, Problem.Amul, Problem.Bmul, map_sub]
    abel
  rw [he, inner_neg_right] at h
  have ht : inner ℝ (x (k+1)-xs) (P.dualResid ρ (z k) (z (k+1))) =
      ρ * inner ℝ (P.Bmul (z (k+1)-z k)) (P.Amul (x (k+1)-xs)) := by
    rw [real_inner_comm]
    simp only [Problem.dualResid, real_inner_smul_left, Problem.ATmul, transpose_inner, Problem.Amul]
  rw [ht]
  linarith


