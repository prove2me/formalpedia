-- Prove2me | solution 1 for DrezetGHZ.product_supported_implies_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-29T00:38:53.590225+00:00
-- url     : https://prove2.me/submissions/f139057f-9d3b-4ce9-81c8-26a970d0f645

import Mathlib

theorem solution (p₁ p₂ p₃ : ℤˣ → ℝ) (s : ℤˣ)
    (h₁ : ∀ α, 0 ≤ p₁ α) (h₂ : ∀ α, 0 ≤ p₂ α) (h₃ : ∀ α, 0 ≤ p₃ α)
    (hs₁ : ∑ α, p₁ α = 1) (hs₂ : ∑ α, p₂ α = 1) (hs₃ : ∑ α, p₃ α = 1)
    (hzero : ∀ α β γ : ℤˣ, α * β * γ ≠ s → p₁ α * p₂ β * p₃ γ = 0) :
    ∃ a₁ a₂ a₃ : ℤˣ, a₁ * a₂ * a₃ = s ∧
      (∀ α, p₁ α = if α = a₁ then 1 else 0) ∧
      (∀ α, p₂ α = if α = a₂ then 1 else 0) ∧
      (∀ α, p₃ α = if α = a₃ then 1 else 0) := by
  have hneg : (-1 : ℤˣ) ≠ 1 := by decide
  have hsum : ∀ p : ℤˣ → ℝ, ∑ α, p α = p 1 + p (-1) := by
    intro p
    rw [UnitsInt.univ, Finset.sum_pair (Ne.symm hneg)]
  have hpos : ∀ p : ℤˣ → ℝ, (∀ α, 0 ≤ p α) → ∑ α, p α = 1 → ∃ a, 0 < p a := by
    intro p hp hs
    rw [hsum] at hs
    by_contra hcon
    push_neg at hcon
    have := hcon 1
    have := hcon (-1)
    linarith
  have hdet : ∀ p : ℤˣ → ℝ, (∀ α, 0 ≤ p α) → ∑ α, p α = 1 → ¬ (0 < p 1 ∧ 0 < p (-1)) →
      ∃ a : ℤˣ, ∀ α, p α = if α = a then 1 else 0 := by
    intro p hp hs hnot
    rw [hsum] at hs
    by_cases h1 : 0 < p 1
    · have h2 : p (-1) = 0 := by
        by_contra h
        exact hnot ⟨h1, lt_of_le_of_ne (hp _) (Ne.symm h)⟩
      refine ⟨1, fun α => ?_⟩
      rcases Int.units_eq_one_or α with rfl | rfl
      · rw [if_pos rfl]; linarith
      · rw [if_neg hneg]; exact h2
    · have h1' : p 1 = 0 := le_antisymm (not_lt.1 h1) (hp 1)
      refine ⟨-1, fun α => ?_⟩
      rcases Int.units_eq_one_or α with rfl | rfl
      · rw [if_neg (Ne.symm hneg)]; exact h1'
      · rw [if_pos rfl]; linarith
  -- flipping one sign changes the product, so a two-point support contradicts `hzero`
  have flip : ∀ x y z : ℤˣ, x * y * z = s → (-x) * y * z ≠ s := by
    intro x y z h h'
    have : (-x) * y * z = x * y * z := h'.trans h.symm
    have hx : -x = x := mul_right_cancel (mul_right_cancel this)
    rcases Int.units_eq_one_or x with rfl | rfl
    · exact hneg hx
    · exact hneg (by simpa using hx.symm)
  obtain ⟨a, ha⟩ := hpos p₁ h₁ hs₁
  obtain ⟨b, hb⟩ := hpos p₂ h₂ hs₂
  obtain ⟨c, hc⟩ := hpos p₃ h₃ hs₃
  have n1 : ¬ (0 < p₁ 1 ∧ 0 < p₁ (-1)) := by
    rintro ⟨x, y⟩
    by_cases hs : 1 * b * c = s
    · have h0 := hzero _ _ _ (flip 1 b c hs)
      have : 0 < p₁ (-1) * p₂ b * p₃ c := mul_pos (mul_pos y hb) hc
      linarith
    · have h0 := hzero _ _ _ hs
      have : 0 < p₁ 1 * p₂ b * p₃ c := mul_pos (mul_pos x hb) hc
      linarith
  have n2 : ¬ (0 < p₂ 1 ∧ 0 < p₂ (-1)) := by
    rintro ⟨x, y⟩
    by_cases hs : 1 * a * c = s
    · have hne : a * (-1) * c ≠ s := by
        intro h; apply flip 1 a c hs; rw [← h]; simp [mul_comm]
      have h0 := hzero _ _ _ hne
      have : 0 < p₁ a * p₂ (-1) * p₃ c := mul_pos (mul_pos ha y) hc
      linarith
    · have hne : a * 1 * c ≠ s := by
        intro h; apply hs; rw [← h]; simp [mul_comm]
      have h0 := hzero _ _ _ hne
      have : 0 < p₁ a * p₂ 1 * p₃ c := mul_pos (mul_pos ha x) hc
      linarith
  have n3 : ¬ (0 < p₃ 1 ∧ 0 < p₃ (-1)) := by
    rintro ⟨x, y⟩
    by_cases hs : 1 * a * b = s
    · have hne : a * b * (-1) ≠ s := by
        intro h; apply flip 1 a b hs; rw [← h]; simp [mul_comm, mul_left_comm]
      have h0 := hzero _ _ _ hne
      have : 0 < p₁ a * p₂ b * p₃ (-1) := mul_pos (mul_pos ha hb) y
      linarith
    · have hne : a * b * 1 ≠ s := by
        intro h; apply hs; rw [← h]; simp [mul_comm]
      have h0 := hzero _ _ _ hne
      have : 0 < p₁ a * p₂ b * p₃ 1 := mul_pos (mul_pos ha hb) x
      linarith
  obtain ⟨a₁, e₁⟩ := hdet p₁ h₁ hs₁ n1
  obtain ⟨a₂, e₂⟩ := hdet p₂ h₂ hs₂ n2
  obtain ⟨a₃, e₃⟩ := hdet p₃ h₃ hs₃ n3
  refine ⟨a₁, a₂, a₃, ?_, e₁, e₂, e₃⟩
  by_contra hne
  have h0 := hzero _ _ _ hne
  rw [e₁, e₂, e₃] at h0
  simp at h0
