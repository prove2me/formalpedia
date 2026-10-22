-- Prove2me | solution 1 for EvenCycleTuran.PathCount.rayleigh_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:00:11.764624+00:00
-- url     : https://prove2.me/submissions/377d6172-e497-4b7b-b298-11704a4183ef

import Mathlib
import Definitions.Def_EvenCycleTuran_PathCount_Setting

set_option autoImplicit false
open EvenCycleTuran.PathCount
open Matrix

theorem ecp_rayleigh (n l : ℕ) (hl : 1 ≤ l) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    (∑ i : Fin n, ∑ j : Fin n, ((G.adjMatrix ℝ) ^ (l - 1)) i j) ≤
      (n : ℝ) * specRad G ^ (l - 1) := by
  classical
  set m := l - 1 with hm
  have hA : (G.adjMatrix ℝ).IsHermitian := G.isHermitian_adjMatrix ℝ
  set ev : Fin n → ℝ := hA.eigenvalues with hev
  set U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hpow : (G.adjMatrix ℝ) ^ m = U * Matrix.diagonal (fun i => ev i ^ m) * star U := by
    have := hA.spectral_theorem
    conv_lhs => rw [this]
    rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.diagonal_pow]
    simp only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq]
    rfl
  set c : Fin n → ℝ := (star U) *ᵥ (fun _ => (1 : ℝ)) with hc
  have hvec : (fun _ => (1 : ℝ)) ᵥ* U = c := by
    rw [hc, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mulVec_transpose]
  have hsum : (∑ i : Fin n, ∑ j : Fin n, ((G.adjMatrix ℝ) ^ m) i j) =
      ∑ i, ev i ^ m * (c i * c i) := by
    have h1 : (∑ i : Fin n, ∑ j : Fin n, ((G.adjMatrix ℝ) ^ m) i j) =
        (fun _ => (1 : ℝ)) ⬝ᵥ (((G.adjMatrix ℝ) ^ m) *ᵥ (fun _ => (1 : ℝ))) := by
      simp [dotProduct, Matrix.mulVec]
    rw [h1, hpow, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hvec,
      ← hc]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hnorm : (∑ i, c i * c i) = n := by
    have : (fun _ => (1 : ℝ)) ⬝ᵥ (U *ᵥ c) = c ⬝ᵥ c := by
      rw [Matrix.dotProduct_mulVec, hvec]
    have h2 : U *ᵥ c = (fun _ => (1 : ℝ)) := by
      rw [hc, Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
    rw [h2] at this
    simp only [dotProduct] at this
    rw [← this]; simp
  rw [hsum]
  have hρ : ∀ i, ev i ^ m ≤ specRad G ^ m := by
    intro i
    have h1 : |ev i| ≤ specRad G := by
      unfold specRad
      exact le_ciSup (f := fun i => |(G.isHermitian_adjMatrix ℝ).eigenvalues i|)
        (Set.finite_range _).bddAbove i
    calc ev i ^ m ≤ |ev i ^ m| := le_abs_self _
      _ = |ev i| ^ m := abs_pow _ _
      _ ≤ specRad G ^ m := pow_le_pow_left₀ (abs_nonneg _) h1 m
  calc ∑ i, ev i ^ m * (c i * c i) ≤ ∑ i, specRad G ^ m * (c i * c i) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hρ i) (mul_self_nonneg _))
    _ = specRad G ^ m * ∑ i, c i * c i := by rw [Finset.mul_sum]
    _ = (n : ℝ) * specRad G ^ m := by rw [hnorm]; ring

theorem solution (n l : ℕ) (hl : 1 ≤ l) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    (∑ i : Fin n, ∑ j : Fin n, ((G.adjMatrix ℝ) ^ (l - 1)) i j) ≤
      (n : ℝ) * specRad G ^ (l - 1) := ecp_rayleigh n l hl G
