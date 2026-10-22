-- Prove2me | solution 2 for FlagshipMEA.Monopoly.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:26:45.744987+00:00
-- url     : https://prove2.me/submissions/b88b2bfb-1107-4b8e-abb4-f4d332f3accb

import Mathlib
set_option autoImplicit false

theorem solution {n : ℕ} (hn : 0 < n) (a b m : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 < b i) (hm : ∀ i, 0 ≤ m i)
    (hM : 0 < ∑ i, m i) :
    ∃ k : Fin n,
      (∀ i, a i / b i ≤ a k / b k) ∧
      (∑ i, m i * a i) / (∑ i, m i * b i) ≤ a k / b k ∧
      ((∑ i, m i * a i) / (∑ i, m i * b i) = a k / b k ↔
        ∀ i, m i ≠ 0 → a i / b i = a k / b k) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨k, hk⟩ := Finite.exists_max (fun i => a i / b i)
  refine ⟨k, hk, ?_⟩
  set r := a k / b k with hr
  have hD : 0 < ∑ i, m i * b i := by
    obtain ⟨j, hj⟩ : ∃ j, 0 < m j := by
      by_contra h
      push_neg at h
      have : ∑ i, m i ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
      linarith
    calc (0:ℝ) < m j * b j := mul_pos hj (hb j)
      _ ≤ ∑ i, m i * b i :=
        Finset.single_le_sum (f := fun i => m i * b i) (fun i _ => mul_nonneg (hm i) (hb i).le)
          (Finset.mem_univ j)
  have key : ∀ i, a i ≤ r * b i := fun i => by
    have := hk i
    rwa [div_le_iff₀ (hb i)] at this
  have hsum : ∑ i, m i * (r * b i - a i) = r * ∑ i, m i * b i - ∑ i, m i * a i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  have hnn : ∀ i, 0 ≤ m i * (r * b i - a i) := fun i =>
    mul_nonneg (hm i) (by linarith [key i])
  have hle : ∑ i, m i * a i ≤ r * ∑ i, m i * b i := by
    have : 0 ≤ ∑ i, m i * (r * b i - a i) := Finset.sum_nonneg (fun i _ => hnn i)
    linarith
  refine ⟨by rw [div_le_iff₀ hD]; linarith, ?_⟩
  rw [div_eq_iff hD.ne']
  constructor
  · intro h i hi
    have h0 : ∑ i, m i * (r * b i - a i) = 0 := by rw [hsum]; linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).1 h0 i (Finset.mem_univ i)
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 hi
    · rw [div_eq_iff (hb i).ne']; linarith
  · intro h
    have h0 : ∑ i, m i * (r * b i - a i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : m i = 0
      · simp [hi]
      · have := h i hi
        rw [div_eq_iff (hb i).ne'] at this
        rw [this]; ring
    linarith
