-- Prove2me | solution 1 for BoydADMM.Convergence.ineq_A2
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:29:29.233248+00:00
-- url     : https://prove2.me/submissions/f57257f7-1d09-44a0-a937-1426b26c53bc

import Definitions.Def_BoydADMM_Convergence_Model
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential
import Theorems.Thm_BoydADMM_Convergence_x_update_dual_residual
import Theorems.Thm_BoydADMM_Convergence_z_update_dual_feasible
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

private lemma saddle_value {n m p : ℕ} (P : Problem n m p)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys) :
    P.optVal = P.f xs + P.g zs := by
  have hf := saddle_feasible P hsp
  have hm : P.f xs + P.g zs ∈ {t : ℝ | ∃ x ∈ P.Cf, ∃ z ∈ P.Cg,
      P.resid x z = 0 ∧ t = P.f x + P.g z} := ⟨xs, hsp.1, zs, hsp.2.1, hf, rfl⟩
  have hlo : ∀ t ∈ {t : ℝ | ∃ x ∈ P.Cf, ∃ z ∈ P.Cg,
      P.resid x z = 0 ∧ t = P.f x + P.g z}, P.f xs + P.g zs ≤ t := by
    rintro t ⟨x, hx, z, hz, hr, rfl⟩
    have h := hsp.2.2.2 x hx z hz
    simpa [Problem.augLag, hf, hr] using h
  exact le_antisymm (csInf_le ⟨P.f xs + P.g zs, hlo⟩ hm) (le_csInf ⟨_, hm⟩ hlo)


end BoydADMM.Convergence
open BoydADMM.Convergence
/-- (A.2), p. 107: for every `k ≥ 0`,
`p^{k+1} − p⋆ ≤ −(y^{k+1})ᵀr^{k+1} − ρ(B(z^{k+1} − z^k))ᵀ(−r^{k+1} + B(z^{k+1} − z⋆))`. -/
theorem solution
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) (k : ℕ) :
    P.f (x (k + 1)) + P.g (z (k + 1)) - P.optVal ≤
      -inner ℝ (y (k + 1)) (P.resid (x (k + 1)) (z (k + 1)))
        - ρ * inner ℝ (P.Bmul (z (k + 1) - z k))
            (-P.resid (x (k + 1)) (z (k + 1)) + P.Bmul (z (k + 1) - zs)) := by
  have hx := x_update_dual_residual P hA1 hρ hrun k xs hsp.1
  have hz := z_update_dual_feasible P hA1 hρ hrun k zs hsp.2.1
  change inner ℝ (P.dualResid ρ (z k) (z (k+1)) - P.ATmul (y (k+1)))
    (xs - x (k+1)) ≤ P.f xs - P.f (x (k+1)) at hx
  change inner ℝ (-P.BTmul (y (k+1))) (zs-z (k+1)) ≤ P.g zs-P.g (z (k+1)) at hz
  simp only [Problem.dualResid, Problem.ATmul, inner_sub_left, real_inner_smul_left,
    transpose_inner] at hx
  simp only [Problem.BTmul, inner_neg_left, transpose_inner] at hz
  have hc : P.c = P.Amul xs + P.Bmul zs := (sub_eq_zero.mp (saddle_feasible P hsp)).symm
  have he : P.Amul (xs-x (k+1)) =
      -P.resid (x (k+1)) (z (k+1)) + P.Bmul (z (k+1)-zs) := by
    simp only [Problem.resid, hc, Problem.Amul, Problem.Bmul, map_sub]
    abel
  have hy : inner ℝ (y (k+1)) (P.Amul (xs-x (k+1))) +
      inner ℝ (y (k+1)) (P.Bmul (zs-z (k+1))) =
      -inner ℝ (y (k+1)) (P.resid (x (k+1)) (z (k+1))) := by
    rw [← inner_add_right]
    have hv : P.Amul (xs-x (k+1)) + P.Bmul (zs-z (k+1)) =
        -P.resid (x (k+1)) (z (k+1)) := by
      simp only [Problem.resid, hc, Problem.Amul, Problem.Bmul, map_sub]
      abel
    rw [hv, inner_neg_right]
  change ρ * inner ℝ (P.Bmul (z (k+1)-z k)) (P.Amul (xs-x (k+1))) -
    inner ℝ (y (k+1)) (P.Amul (xs-x (k+1))) ≤ _ at hx
  change -inner ℝ (y (k+1)) (P.Bmul (zs-z (k+1))) ≤ _ at hz
  rw [saddle_value P hsp]
  nlinarith [congrArg (fun v => inner ℝ (P.Bmul (z (k+1)-z k)) v) he]


