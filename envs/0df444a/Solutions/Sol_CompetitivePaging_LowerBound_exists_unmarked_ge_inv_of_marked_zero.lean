-- Prove2me | solution 1 for CompetitivePaging.LowerBound.exists_unmarked_ge_inv_of_marked_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:00:00.717213+00:00
-- url     : https://prove2.me/submissions/06c91a61-6497-4243-9d8f-f5e80572546e

import Mathlib

theorem solution {M : Type} [Fintype M] (p : M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (S : Finset M)
    (hS : S.card < Fintype.card M) (hP : ∑ i ∈ S, p i = 0) :
    ∃ i ∉ S, 1 / ((Fintype.card M : ℝ) - S.card) ≤ p i := by
  classical
  have hsplit : ∑ i ∈ Sᶜ, p i = 1 := by
    have h := Finset.sum_add_sum_compl S p
    rw [hP, hsum] at h
    linarith
  have hcardc : Sᶜ.card = Fintype.card M - S.card := Finset.card_compl S
  have hcpos : 0 < Sᶜ.card := by rw [hcardc]; omega
  have ht : ((Sᶜ.card : ℕ) : ℝ) = (Fintype.card M : ℝ) - S.card := by
    rw [hcardc, Nat.cast_sub (R := ℝ) hS.le]
  have htpos : 0 < (Fintype.card M : ℝ) - S.card := by
    rw [← ht]; exact_mod_cast hcpos
  have hne : Sᶜ.Nonempty := Finset.card_pos.mp hcpos
  have key : ∑ _i ∈ Sᶜ, (1 / ((Fintype.card M : ℝ) - S.card)) ≤ ∑ i ∈ Sᶜ, p i := by
    refine le_of_eq ?_
    rw [Finset.sum_const, hsplit, nsmul_eq_mul, ht]
    field_simp
  obtain ⟨i, hi, hle⟩ := Finset.exists_le_of_sum_le hne key
  exact ⟨i, Finset.mem_compl.mp hi, hle⟩
