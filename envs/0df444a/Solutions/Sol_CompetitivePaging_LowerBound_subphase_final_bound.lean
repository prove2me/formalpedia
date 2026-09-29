-- Prove2me | solution 1 for CompetitivePaging.LowerBound.subphase_final_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:07:46.764064+00:00
-- url     : https://prove2.me/submissions/f555df32-ad81-4607-89d9-df566447d898

import Mathlib

theorem solution {M : Type} [Fintype M] (p : M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (S : Finset M)
    (hS : S.card < Fintype.card M) (ε : ℝ) (hε : 0 ≤ ε) (hPε : ∑ i ∈ S, p i ≤ ε)
    (j : M) (hj : j ∉ S) (hmax : ∀ j' ∉ S, p j' ≤ p j) :
    ε + p j ≥ ε + (1 - ∑ i ∈ S, p i) / ((Fintype.card M : ℝ) - S.card) ∧
    ε + (1 - ∑ i ∈ S, p i) / ((Fintype.card M : ℝ) - S.card) ≥
      ε + (1 - ε) / ((Fintype.card M : ℝ) - S.card) ∧
    ε + (1 - ε) / ((Fintype.card M : ℝ) - S.card) ≥
      1 / ((Fintype.card M : ℝ) - S.card) := by
  classical
  have hsplit : ∑ i ∈ Sᶜ, p i = 1 - ∑ i ∈ S, p i := by
    have h := Finset.sum_add_sum_compl S p
    rw [hsum] at h
    linarith
  have hcardc : Sᶜ.card = Fintype.card M - S.card := Finset.card_compl S
  have hcpos : 0 < Sᶜ.card := by rw [hcardc]; omega
  have ht : ((Sᶜ.card : ℕ) : ℝ) = (Fintype.card M : ℝ) - S.card := by
    rw [hcardc, Nat.cast_sub (R := ℝ) hS.le]
  have htpos : 0 < (Fintype.card M : ℝ) - S.card := by
    rw [← ht]; exact_mod_cast hcpos
  have hone : (1 : ℝ) ≤ (Fintype.card M : ℝ) - S.card := by
    have h1 : (1 : ℕ) ≤ Sᶜ.card := hcpos
    have : ((1 : ℕ) : ℝ) ≤ ((Sᶜ.card : ℕ) : ℝ) := by exact_mod_cast h1
    rw [ht] at this; simpa using this
  refine ⟨?_, ?_, ?_⟩
  · have hbound : ∑ i ∈ Sᶜ, p i ≤ ((Fintype.card M : ℝ) - S.card) * p j := by
      calc ∑ i ∈ Sᶜ, p i ≤ ∑ _i ∈ Sᶜ, p j :=
            Finset.sum_le_sum fun i hi => hmax i (Finset.mem_compl.mp hi)
        _ = ((Fintype.card M : ℝ) - S.card) * p j := by
            rw [Finset.sum_const, nsmul_eq_mul, ht]
    have hdiv : (1 - ∑ i ∈ S, p i) / ((Fintype.card M : ℝ) - S.card) ≤ p j := by
      rw [div_le_iff₀ htpos]
      nlinarith [hsplit, hbound]
    linarith
  · have hstep : (1 - ε) / ((Fintype.card M : ℝ) - S.card)
        ≤ (1 - ∑ i ∈ S, p i) / ((Fintype.card M : ℝ) - S.card) := by
      gcongr
    linarith
  · rw [ge_iff_le, div_le_iff₀ htpos]
    have hx : (ε + (1 - ε) / ((Fintype.card M : ℝ) - S.card))
        * ((Fintype.card M : ℝ) - S.card)
        = ε * ((Fintype.card M : ℝ) - S.card) + (1 - ε) := by
      field_simp
    rw [hx]
    nlinarith [hε, hone]
