-- Prove2me | solution 1 for CompetitivePaging.LowerBound.max_unmarked_ge_avg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T21:52:53.638715+00:00
-- url     : https://prove2.me/submissions/f3db2dfe-8932-4993-902b-e7c2f2ab3bbd

import Mathlib

theorem solution {M : Type} [Fintype M] (p : M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (S : Finset M)
    (hS : S.card < Fintype.card M) (j : M) (hj : j ∉ S) (hmax : ∀ j' ∉ S, p j' ≤ p j) :
    (1 - ∑ i ∈ S, p i) / ((Fintype.card M : ℝ) - S.card) ≤ p j := by
  classical
  have hsplit : ∑ i ∈ Sᶜ, p i = 1 - ∑ i ∈ S, p i := by
    have h := Finset.sum_add_sum_compl S p
    rw [hsum] at h
    linarith
  have hcardc : Sᶜ.card = Fintype.card M - S.card := Finset.card_compl S
  have hcpos : 0 < Sᶜ.card := by rw [hcardc]; omega
  have ht : ((Sᶜ.card : ℕ) : ℝ) = (Fintype.card M : ℝ) - S.card := by
    rw [hcardc, Nat.cast_sub hS.le]
  have htpos : 0 < (Fintype.card M : ℝ) - S.card := by
    rw [← ht]; exact_mod_cast hcpos
  have hbound : ∑ i ∈ Sᶜ, p i ≤ ((Fintype.card M : ℝ) - S.card) * p j := by
    calc ∑ i ∈ Sᶜ, p i ≤ ∑ _i ∈ Sᶜ, p j :=
          Finset.sum_le_sum fun i hi => hmax i (Finset.mem_compl.mp hi)
      _ = ((Fintype.card M : ℝ) - S.card) * p j := by
          rw [Finset.sum_const, nsmul_eq_mul, ht]
  rw [div_le_iff₀ htpos]
  have hcomm : ((Fintype.card M : ℝ) - S.card) * p j = p j * ((Fintype.card M : ℝ) - S.card) := by
    ring
  linarith [hsplit, hbound]
