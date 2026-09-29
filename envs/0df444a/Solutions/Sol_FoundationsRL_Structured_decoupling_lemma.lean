-- Prove2me | solution 1 for FoundationsRL.Structured.decoupling_lemma
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:48:54.581359+00:00
-- url     : https://prove2.me/submissions/ea0cd2eb-4944-437f-aeeb-36c2397adc3c

import Mathlib

namespace FoundationsRL.Structured

end FoundationsRL.Structured

open FoundationsRL.Structured

theorem solution {A : ℕ} {ι : Type*} [Fintype ι] (F : Set (Fin A → ℝ))
    (f : ι → Fin A → ℝ) (hf : ∀ i, f i ∈ F)
    (piStar : (Fin A → ℝ) → Fin A) (hpiStar : ∀ i, ∀ π, f i π ≤ f i (piStar (f i)))
    (ν : ι → ℝ) (hν_nonneg : ∀ i, 0 ≤ ν i) (hν_sum : ∑ i, ν i = 1)
    (p : Fin A → ℝ) (hp : ∀ π, p π = ∑ i, ν i * (if piStar (f i) = π then 1 else 0))
    (fbar : Fin A → ℝ) :
    ∑ i, ν i * (f i (piStar (f i)) - fbar (piStar (f i))) ≤
      Real.sqrt ((A : ℝ) * ∑ i, ν i * ∑ π, p π * (f i π - fbar π) ^ 2) := by
  have hw0 : ∀ π i, 0 ≤ ν i * (if piStar (f i) = π then (1:ℝ) else 0) :=
    fun π i => mul_nonneg (hν_nonneg i) (by split_ifs <;> norm_num)
  have hwle : ∀ π i, ν i * (if piStar (f i) = π then (1:ℝ) else 0) ≤ ν i := fun π i => by
    split_ifs <;> simp [hν_nonneg i]
  have hL : ∑ i, ν i * (f i (piStar (f i)) - fbar (piStar (f i))) =
      ∑ π, ∑ i, (ν i * (if piStar (f i) = π then (1:ℝ) else 0)) * (f i π - fbar π) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    congr 1
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp
  have hCS : ∀ π, (∑ i, (ν i * (if piStar (f i) = π then (1:ℝ) else 0)) * (f i π - fbar π)) ^ 2
      ≤ p π * ∑ i, ν i * (f i π - fbar π) ^ 2 := by
    intro π
    have h1 : (∑ i, (ν i * (if piStar (f i) = π then (1:ℝ) else 0)) * (f i π - fbar π)) ^ 2 ≤
        (∑ i, ν i * (if piStar (f i) = π then (1:ℝ) else 0)) *
          ∑ i, (ν i * (if piStar (f i) = π then (1:ℝ) else 0)) * (f i π - fbar π) ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => hw0 π i)
        (fun i _ => mul_nonneg (hw0 π i) (sq_nonneg _)) (fun i _ => le_of_eq (by ring))
    rw [hp π]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun i _ => hw0 π i))
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hwle π i) (sq_nonneg _)
  have hsq : (∑ π, ∑ i, (ν i * (if piStar (f i) = π then (1:ℝ) else 0)) * (f i π - fbar π)) ^ 2
      ≤ (A : ℝ) * ∑ i, ν i * ∑ π, p π * (f i π - fbar π) ^ 2 := by
    have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun π => ∑ i, (ν i * (if piStar (f i) = π then (1:ℝ) else 0)) * (f i π - fbar π))
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    calc _ ≤ ∑ π, p π * ∑ i, ν i * (f i π - fbar π) ^ 2 :=
          Finset.sum_le_sum fun π _ => hCS π
      _ = ∑ i, ν i * ∑ π, p π * (f i π - fbar π) ^ 2 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun π _ => by ring
  rw [hL]
  exact (le_abs_self _).trans (Real.abs_le_sqrt hsq)
