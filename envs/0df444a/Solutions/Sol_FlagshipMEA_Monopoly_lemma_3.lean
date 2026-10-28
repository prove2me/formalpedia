-- Prove2me | solution 1 for FlagshipMEA.Monopoly.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T16:19:43.953354+00:00
-- url     : https://prove2.me/submissions/4b014a1e-6725-4800-bfe2-143a8ff8edb3

import Mathlib

theorem solution {n : ℕ} (hn : 0 < n) (a b m : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 < b i) (hm : ∀ i, 0 ≤ m i)
    (hM : 0 < ∑ i, m i) :
    ∃ k : Fin n,
      (∀ i, a i / b i ≤ a k / b k) ∧
      (∑ i, m i * a i) / (∑ i, m i * b i) ≤ a k / b k ∧
      ((∑ i, m i * a i) / (∑ i, m i * b i) = a k / b k ↔
        ∀ i, m i ≠ 0 → a i / b i = a k / b k) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun i => a i / b i)
    Finset.univ_nonempty
  have hk' : ∀ i, a i / b i ≤ a k / b k := fun i => hk i (Finset.mem_univ i)
  set r := a k / b k with hr
  have hai : ∀ i, a i ≤ r * b i := by
    intro i
    have := hk' i
    rwa [div_le_iff₀ (hb i)] at this
  have hMB : 0 < ∑ i, m i * b i := by
    obtain ⟨j, -, hj0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hM.ne'
    have hj : 0 < m j := lt_of_le_of_ne (hm j) (Ne.symm hj0)
    exact lt_of_lt_of_le (mul_pos hj (hb j))
      (Finset.single_le_sum (f := fun i => m i * b i)
        (fun i _ => mul_nonneg (hm i) (hb i).le) (Finset.mem_univ j))
  have hterm : ∀ i, 0 ≤ m i * (r * b i - a i) := fun i =>
    mul_nonneg (hm i) (by linarith [hai i])
  have hdiff : r * ∑ i, m i * b i - ∑ i, m i * a i = ∑ i, m i * (r * b i - a i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨k, hk', ?_, ?_⟩
  · rw [div_le_iff₀ hMB]
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hterm i)
    linarith
  · rw [div_eq_iff hMB.ne']
    constructor
    · intro heq i hi
      have hsum0 : ∑ i, m i * (r * b i - a i) = 0 := by rw [← hdiff]; linarith
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hterm i)).1
        hsum0 i (Finset.mem_univ i)
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hi
      · rw [div_eq_iff (hb i).ne']
        linarith
    · intro hall
      have hsum0 : ∑ i, m i * (r * b i - a i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        by_cases hi : m i = 0
        · rw [hi, zero_mul]
        · have := hall i hi
          rw [div_eq_iff (hb i).ne'] at this
          rw [this]; ring
      linarith
