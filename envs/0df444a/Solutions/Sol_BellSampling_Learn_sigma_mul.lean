-- Prove2me | solution 1 for BellSampling.Learn.sigma_mul
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:24:58.091649+00:00
-- url     : https://prove2.me/submissions/16ea4ead-91d4-4ab1-a5dc-5d2e89297d57

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
open StabilizerRank

namespace Aux_Bell_sigma
open BellSampling.Learn

lemma cases4 : ∀ c : ZMod 2 × ZMod 2, c = (0, 0) ∨ c = (0, 1) ∨ c = (1, 0) ∨ c = (1, 1) := by
  decide

lemma single (c d : ZMod 2 × ZMod 2) : ∃ e : ℂ, (e = 1 ∨ e = -1) ∧
    ∀ a b : Bool, ∑ z : Bool, sigma1 c a z * sigma1 d z b = e * sigma1 (c + d) a b := by
  rcases cases4 c with rfl | rfl | rfl | rfl <;> rcases cases4 d with rfl | rfl | rfl | rfl
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro a b; cases a <;> cases b <;> simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, Fintype.sum_bool, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide, show ((0, 0) + (0, 0) : ZMod 2 × ZMod 2) = (0, 0) by decide]
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro a b; cases a <;> cases b <;> simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, Fintype.sum_bool, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide, show ((0, 0) + (0, 1) : ZMod 2 × ZMod 2) = (0, 1) by decide]
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro a b; cases a <;> cases b <;> simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, Fintype.sum_bool, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide, show ((0, 0) + (1, 0) : ZMod 2 × ZMod 2) = (1, 0) by decide]
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro a b; cases a <;> cases b <;> simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, Fintype.sum_bool, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide, show ((0, 0) + (1, 1) : ZMod 2 × ZMod 2) = (1, 1) by decide]
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro a b; cases a <;> cases b <;> simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, Fintype.sum_bool, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide, show ((0, 1) + (0, 0) : ZMod 2 × ZMod 2) = (0, 1) by decide]
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro a b; cases a <;> cases b <;> simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, Fintype.sum_bool, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide, show ((0, 1) + (0, 1) : ZMod 2 × ZMod 2) = (0, 0) by decide]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro a b; cases a <;> cases b <;> simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, Fintype.sum_bool, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide, show ((0, 1) + (1, 0) : ZMod 2 × ZMod 2) = (1, 1) by decide]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro a b; cases a <;> cases b <;> simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, Fintype.sum_bool, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide, show ((0, 1) + (1, 1) : ZMod 2 × ZMod 2) = (1, 0) by decide]
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro a b; cases a <;> cases b <;> simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, Fintype.sum_bool, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide, show ((1, 0) + (0, 0) : ZMod 2 × ZMod 2) = (1, 0) by decide]
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro a b; cases a <;> cases b <;> simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, Fintype.sum_bool, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide, show ((1, 0) + (0, 1) : ZMod 2 × ZMod 2) = (1, 1) by decide]
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro a b; cases a <;> cases b <;> simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, Fintype.sum_bool, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide, show ((1, 0) + (1, 0) : ZMod 2 × ZMod 2) = (0, 0) by decide]
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro a b; cases a <;> cases b <;> simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, Fintype.sum_bool, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide, show ((1, 0) + (1, 1) : ZMod 2 × ZMod 2) = (0, 1) by decide]
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro a b; cases a <;> cases b <;> simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, Fintype.sum_bool, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide, show ((1, 1) + (0, 0) : ZMod 2 × ZMod 2) = (1, 1) by decide]
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro a b; cases a <;> cases b <;> simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, Fintype.sum_bool, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide, show ((1, 1) + (0, 1) : ZMod 2 × ZMod 2) = (1, 0) by decide]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro a b; cases a <;> cases b <;> simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, Fintype.sum_bool, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide, show ((1, 1) + (1, 0) : ZMod 2 × ZMod 2) = (0, 1) by decide]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro a b; cases a <;> cases b <;> simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, Fintype.sum_bool, show ((0, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 0) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 0) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (0, 1) by decide, show ((1, 1) : ZMod 2 × ZMod 2) ≠ (1, 0) by decide, show ((1, 1) + (1, 1) : ZMod 2 × ZMod 2) = (0, 0) by decide]

end Aux_Bell_sigma

open BellSampling.Learn in
theorem solution {n : ℕ} (s t : PStr n) :
    sigma s * sigma t = sigma (s + t) ∨ sigma s * sigma t = -sigma (s + t) := by
  choose e he hmul using Aux_Bell_sigma.single
  have hprod : ∀ x y : StabilizerRank.Bits n, (sigma s * sigma t) x y =
      (∏ i, e (s i) (t i)) * sigma (s + t) x y := by
    intro x y
    rw [Matrix.mul_apply]
    simp only [sigma, Matrix.of_apply]
    have h1 : ∀ z : StabilizerRank.Bits n, (∏ i, sigma1 (s i) (x i) (z i)) *
        (∏ i, sigma1 (t i) (z i) (y i)) =
        ∏ i, (sigma1 (s i) (x i) (z i) * sigma1 (t i) (z i) (y i)) := by
      intro z; rw [← Finset.prod_mul_distrib]
    simp_rw [h1]
    rw [← Fintype.prod_sum (fun i c => sigma1 (s i) (x i) c * sigma1 (t i) c (y i))]
    simp_rw [hmul]
    rw [Finset.prod_mul_distrib]
    rfl
  have hpm : (∏ i, e (s i) (t i)) = 1 ∨ (∏ i, e (s i) (t i)) = -1 := by
    apply Finset.prod_induction _ (fun z : ℂ => z = 1 ∨ z = -1)
    · rintro a b (rfl | rfl) (rfl | rfl) <;> simp
    · left; rfl
    · intro i _; exact he _ _
  rcases hpm with h | h
  · left; ext x y; rw [hprod, h, one_mul]
  · right; ext x y; rw [hprod, h, neg_one_mul]; rfl
