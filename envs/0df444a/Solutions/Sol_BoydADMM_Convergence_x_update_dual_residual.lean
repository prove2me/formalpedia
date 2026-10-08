-- Prove2me | solution 1 for BoydADMM.Convergence.x_update_dual_residual
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:25:46.414323+00:00
-- url     : https://prove2.me/submissions/3e5ad7ae-7c2c-4bda-a737-d39a49728a75

import Definitions.Def_BoydADMM_Convergence_Model
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential
open Filter
open scoped Topology
namespace BoydADMM.Convergence

private lemma transpose_inner {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ)
    (u : EuclideanSpace ℝ (Fin a)) (v : EuclideanSpace ℝ (Fin b)) :
    inner ℝ (Matrix.toEuclideanLin M.transpose u) v = inner ℝ u (Matrix.toEuclideanLin M v) := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]

private lemma norm_affine_sq {a : ℕ} (r d : EuclideanSpace ℝ (Fin a)) (t : ℝ) :
    ‖r + t • d‖ ^ 2 = ‖r‖ ^ 2 + 2 * t * inner ℝ r d + t ^ 2 * ‖d‖ ^ 2 := by
  simp [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, real_inner_smul_right]
  ring

private lemma quadratic_min_support {a b : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin a))} {f : EuclideanSpace ℝ (Fin a) → ℝ}
    (hf : ConvexOn ℝ C f) {u : EuclideanSpace ℝ (Fin a)} (hu : u ∈ C)
    (L : EuclideanSpace ℝ (Fin a) →ₗ[ℝ] EuclideanSpace ℝ (Fin b))
    (r y : EuclideanSpace ℝ (Fin b)) (ρ : ℝ)
    (hmin : ∀ v ∈ C, f u + inner ℝ y r + (ρ / 2) * ‖r‖ ^ 2 ≤
      f v + inner ℝ y (r + L (v - u)) + (ρ / 2) * ‖r + L (v - u)‖ ^ 2) :
    ∀ v ∈ C, -inner ℝ (y + ρ • r) (L (v - u)) ≤ f v - f u := by
  intro v hv
  let d := L (v - u)
  have hseg (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
      -(f v - f u + inner ℝ (y + ρ • r) d + t * (ρ / 2) * ‖d‖ ^ 2) ≤ 0 := by
    have hc := hf.2 hu hv (show 0 ≤ 1-t by linarith) ht.le (show 1-t+t=1 by ring)
    have hm := hmin ((1-t) • u + t • v) (hf.1 hu hv (by linarith) ht.le (by ring))
    have he : L ((1-t) • u + t • v - u) = t • d := by
      dsimp [d]
      rw [show (1-t) • u + t • v - u = t • (v-u) by module]
      exact L.map_smul t (v-u)
    rw [he, norm_affine_sq] at hm
    simp only [inner_add_right, real_inner_smul_right,
      smul_eq_mul] at hm hc
    simp only [inner_add_left, real_inner_smul_left]
    have hmul : 0 ≤ t * (f v - f u + inner ℝ y d + ρ * inner ℝ r d +
        t * (ρ / 2) * ‖d‖ ^ 2) := by nlinarith [hc, hm]
    have := (mul_nonneg_iff_of_pos_left ht).mp hmul
    linarith
  have hlim : Tendsto (fun t : ℝ => -(f v - f u + inner ℝ (y + ρ • r) d +
      t * (ρ / 2) * ‖d‖ ^ 2)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-(f v - f u + inner ℝ (y + ρ • r) d))) := by
    have hc : ContinuousAt (fun t : ℝ => -(f v - f u +
      inner ℝ (y + ρ • r) d + t * (ρ / 2) * ‖d‖ ^ 2)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      -(f v - f u + inner ℝ (y + ρ • r) d + t * (ρ / 2) * ‖d‖ ^ 2) ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0:ℝ)<1 by norm_num))] with t ht ht1
    exact hseg t ht ht1
  have := le_of_tendsto hlim he
  dsimp [d] at this
  linarith


end BoydADMM.Convergence
open BoydADMM.Convergence
/-- §3.3, p. 18: `ρAᵀB(z^{k+1} − z^k) ∈ ∂f(x^{k+1}) + Aᵀy^{k+1}`, i.e.
`s^{k+1} − Aᵀy^{k+1} ∈ ∂f(x^{k+1})`, for every `k ≥ 0`. -/
theorem solution
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) (k : ℕ) :
    P.dualResid ρ (z k) (z (k + 1)) - P.ATmul (y (k + 1)) ∈
      ShorNonsmooth.Subdiff.subdifferential P.Cf P.f (x (k + 1)) := by
  intro v hv
  have hs := quadratic_min_support hA1.1.convexOn (hrun.x_mem k)
    (Matrix.toEuclideanLin P.A) (P.resid (x (k+1)) (z k)) (y k) ρ
    (fun w hw => by
      have hm := hrun.x_min k w hw
      have he : P.resid (x (k+1)) (z k) +
          Matrix.toEuclideanLin P.A (w-x (k+1)) = P.resid w (z k) := by
        simp only [Problem.resid, Problem.Amul, map_sub]
        abel
      rw [he]
      dsimp [Problem.augLag] at hm
      linarith) v hv
  have he : y k + ρ • P.resid (x (k+1)) (z k) =
      y (k+1) - ρ • P.Bmul (z (k+1)-z k) := by
    rw [hrun.y_succ k]
    simp only [Problem.resid, Problem.Bmul, map_sub]
    module
  rw [he] at hs
  simpa only [Problem.dualResid, Problem.ATmul, inner_sub_left, real_inner_smul_left,
    transpose_inner, Problem.Amul, neg_sub] using hs


