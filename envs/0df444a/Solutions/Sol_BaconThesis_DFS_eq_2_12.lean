-- Prove2me | solution 1 for BaconThesis.DFS.eq_2_12
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T21:59:55.04661+00:00
-- url     : https://prove2.me/submissions/7aff4dd1-9c8b-449e-87b3-e5af5d13d965

import Mathlib
import Definitions.Def_BaconThesis_DFS_osrOp

open scoped Matrix Kronecker

set_option linter.unusedSectionVars false

namespace BaconThesis.DFS.SolM2_12

open BaconThesis.DFS

variable {s e : Type} [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]

/-- The isometry-like embedding `I ⊗ |ψ⟩`. -/
def K (s : Type) [DecidableEq s] (ψ : e → ℂ) : Matrix (s × e) s ℂ := Matrix.of fun p b => if p.1 = b then ψ p.2 else 0

lemma star_ite0 (p : Prop) [Decidable p] (x : ℂ) :
    (starRingEnd ℂ) (if p then x else 0) = if p then (starRingEnd ℂ) x else 0 := by
  split_ifs <;> simp

lemma osrOp_eq (H : Matrix (s × e) (s × e) ℂ) (t : ℝ) (φ ψ : e → ℂ) :
    osrOp H t φ ψ = (K s φ).conjTranspose * evolOp H t * K s ψ := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [osrOp, K, Matrix.of_apply, Fintype.sum_prod_type, Finset.sum_mul, star_ite0, ite_mul,
    zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, mul_ite, mul_zero, RCLike.star_def]
  rw [Finset.sum_comm]

lemma sum_K_mul_K {μ : Type} [Fintype μ] (φ : μ → e → ℂ)
    (hφ : ∑ m, Matrix.vecMulVec (φ m) (star (φ m)) = 1) :
    ∑ m, K s (φ m) * (K s (φ m)).conjTranspose = 1 := by
  have h : ∀ k l, ∑ m, φ m k * star (φ m l) = if k = l then 1 else 0 := by
    intro k l
    have := congrFun (congrFun hφ k) l
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.one_apply] using this
  ext ⟨c, k⟩ ⟨d, l⟩
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [K, Matrix.of_apply, star_ite0, RCLike.star_def, mul_ite, ite_mul, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.one_apply, Prod.mk.injEq]
  by_cases hcd : c = d
  · subst hcd
    simpa using h k l
  · simp [hcd]

lemma K_mul_K (ψ : e → ℂ) :
    (K s ψ).conjTranspose * K s ψ = (star ψ ⬝ᵥ ψ) • (1 : Matrix s s ℂ) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [K, Matrix.of_apply, Fintype.sum_prod_type, star_ite0, RCLike.star_def, mul_ite,
    ite_mul, zero_mul, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    simp [dotProduct, mul_comm]
  · simp [hab, Ne.symm hab]

lemma evolOp_unitary (H : Matrix (s × e) (s × e) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    (evolOp H t)ᴴ * evolOp H t = 1 := by
  have hs : star (-(t : ℂ) * Complex.I) = (t : ℂ) * Complex.I := by simp
  rw [evolOp, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH.eq, hs,
    ← Matrix.exp_add_of_commute]
  · rw [← add_smul]
    simp
  · exact (Commute.refl H).smul_left _ |>.smul_right _

end BaconThesis.DFS.SolM2_12

open BaconThesis.DFS BaconThesis.DFS.SolM2_12 in
theorem solution {s e κ μ : Type} [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]
    [Fintype κ] [Fintype μ]
    (H : Matrix (s × e) (s × e) ℂ) (hH : H.IsHermitian) (t : ℝ)
    (φ : μ → e → ℂ) (hφ : ∑ m, Matrix.vecMulVec (φ m) (star (φ m)) = 1)
    (ψ : κ → e → ℂ) (hψ : ∑ ν, star (ψ ν) ⬝ᵥ ψ ν = 1) :
    ∑ m, ∑ ν, (osrOp H t (φ m) (ψ ν))ᴴ * osrOp H t (φ m) (ψ ν) = 1 := by
  rw [Finset.sum_comm]
  have h1 : ∀ ν, ∑ m, (osrOp H t (φ m) (ψ ν))ᴴ * osrOp H t (φ m) (ψ ν) =
      (star (ψ ν) ⬝ᵥ ψ ν) • (1 : Matrix s s ℂ) := by
    intro ν
    have : ∀ m, (osrOp H t (φ m) (ψ ν))ᴴ * osrOp H t (φ m) (ψ ν) =
        (K s (ψ ν)).conjTranspose * (evolOp H t)ᴴ *
          (K s (φ m) * (K s (φ m)).conjTranspose) * (evolOp H t * K s (ψ ν)) := by
      intro m
      simp only [osrOp_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    simp only [this]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, sum_K_mul_K φ hφ, Matrix.mul_one, Matrix.mul_assoc,
      ← Matrix.mul_assoc (evolOp H t)ᴴ, evolOp_unitary H hH, Matrix.one_mul, K_mul_K]
  simp only [h1, ← Finset.sum_smul, hψ, one_smul]
