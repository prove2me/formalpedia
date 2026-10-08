-- Prove2me | solution 1 for BoydADMM.Convergence.ineq_A3
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:25:49.060433+00:00
-- url     : https://prove2.me/submissions/e3a10d3e-ff00-4204-85c9-a7998c9b0aa7

import Definitions.Def_BoydADMM_Convergence_Model
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential
open Filter
open scoped Topology
namespace BoydADMM.Convergence

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
/-- (A.3), p. 107: `p⋆ − p^{k+1} ≤ y⋆ᵀr^{k+1}` for every `k ≥ 0`, where
`p^{k+1} = f(x^{k+1}) + g(z^{k+1})` and `r^{k+1} = Ax^{k+1} + Bz^{k+1} − c`. -/
theorem solution
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {xs : EuclideanSpace ℝ (Fin n)} {zs : EuclideanSpace ℝ (Fin m)}
    {ys : EuclideanSpace ℝ (Fin p)} (hsp : P.IsSaddlePoint xs zs ys)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) (k : ℕ) :
    P.optVal - (P.f (x (k + 1)) + P.g (z (k + 1))) ≤
      inner ℝ ys (P.resid (x (k + 1)) (z (k + 1))) := by
  rw [saddle_value P hsp]
  have h := hsp.2.2.2 _ (hrun.x_mem k) _ (hrun.z_mem k)
  have hf := saddle_feasible P hsp
  simp only [Problem.augLag, hf, inner_zero_right, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div, zero_mul, add_zero] at h
  linarith


