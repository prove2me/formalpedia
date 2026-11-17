-- Prove2me | solution 1 for BaconThesis.DFS.eq_2_9_2_11
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T21:58:21.403189+00:00
-- url     : https://prove2.me/submissions/8ddefad8-010e-496d-a233-ed9e319d8bd9

import Mathlib
import Definitions.Def_BaconThesis_DFS_osrEvolve
import Definitions.Def_BaconThesis_DFS_osrOp

open scoped Matrix Kronecker

set_option linter.unusedSectionVars false

namespace BaconThesis.DFS.SolM2_9

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

lemma kron_eq (ρ : Matrix s s ℂ) (ψ : e → ℂ) :
    ρ ⊗ₖ Matrix.vecMulVec ψ (star ψ) = K s ψ * ρ * (K s ψ).conjTranspose := by
  ext ⟨a, k⟩ ⟨b, l⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp [K, Matrix.vecMulVec_apply, star_ite0, mul_ite]
  ring

lemma ptr_eq {μ : Type} [Fintype μ] (φ : μ → e → ℂ)
    (hφ : ∑ m, Matrix.vecMulVec (φ m) (star (φ m)) = 1) (X : Matrix (s × e) (s × e) ℂ) :
    WildeQIT.partialTraceRight X = ∑ m, (K s (φ m)).conjTranspose * X * K s (φ m) := by
  have h : ∀ k l, ∑ m, φ m l * star (φ m k) = if l = k then 1 else 0 := by
    intro k l
    have := congrFun (congrFun hφ l) k
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.one_apply] using this
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply]
  simp only [WildeQIT.partialTraceRight, K, Matrix.of_apply, Fintype.sum_prod_type,
    Finset.sum_mul, star_ite0, ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite, mul_zero, RCLike.star_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  have : ∀ k, ∑ m, (starRingEnd ℂ) (φ m k) * X (a, k) (b, l) * φ m l =
      X (a, k) (b, l) * if l = k then 1 else 0 := by
    intro k
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [RCLike.star_def]
    ring
  simp [this]


lemma kron_sum {κ : Type} [Fintype κ] (ρ : Matrix s s ℂ) (X : κ → Matrix e e ℂ) :
    ρ ⊗ₖ (∑ ν, X ν) = ∑ ν, ρ ⊗ₖ X ν := by
  ext ⟨a, k⟩ ⟨b, l⟩
  simp [Matrix.sum_apply, Finset.mul_sum]

end BaconThesis.DFS.SolM2_9

open BaconThesis.DFS BaconThesis.DFS.SolM2_9 in
theorem solution {s e κ μ : Type} [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]
    [Fintype κ] [Fintype μ]
    (H : Matrix (s × e) (s × e) ℂ) (t : ℝ)
    (φ : μ → e → ℂ) (hφ : ∑ m, Matrix.vecMulVec (φ m) (star (φ m)) = 1)
    (ψ : κ → e → ℂ) (ρ : Matrix s s ℂ) :
    osrEvolve H (∑ ν, Matrix.vecMulVec (ψ ν) (star (ψ ν))) t ρ =
      ∑ m, ∑ ν, osrOp H t (φ m) (ψ ν) * ρ * (osrOp H t (φ m) (ψ ν))ᴴ := by
  rw [osrEvolve, ptr_eq φ hφ, kron_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [kron_eq, Finset.mul_sum, Finset.sum_mul, osrOp_eq, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [Matrix.sum_mul, Matrix.mul_sum]
  simp only [Matrix.mul_assoc]
