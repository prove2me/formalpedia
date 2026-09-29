-- Prove2me | solution 1 for CompetitivePaging.LowerBound.max_marked_ge_eps_div_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T21:53:48.273199+00:00
-- url     : https://prove2.me/submissions/8b094df2-ea37-4687-9bee-bf465b5ad180

import Mathlib

theorem solution {M : Type} [Fintype M] (p : M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (S : Finset M) (ε : ℝ) (hε : 0 < ε)
    (hP : ε < ∑ j ∈ S, p j) (i : M) (hi : i ∈ S) (hmax : ∀ j ∈ S, p j ≤ p i) :
    ε / S.card ≤ p i ∧ 0 < ε / S.card := by
  have hne : S.Nonempty := ⟨i, hi⟩
  have hcard : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hbound : ∑ j ∈ S, p j ≤ (S.card : ℝ) * p i := by
    calc ∑ j ∈ S, p j ≤ ∑ _j ∈ S, p i := Finset.sum_le_sum hmax
      _ = (S.card : ℝ) * p i := by rw [Finset.sum_const, nsmul_eq_mul]
  refine ⟨?_, div_pos hε hcard⟩
  rw [div_le_iff₀ hcard]
  have hcomm : (S.card : ℝ) * p i = p i * (S.card : ℝ) := by ring
  linarith
