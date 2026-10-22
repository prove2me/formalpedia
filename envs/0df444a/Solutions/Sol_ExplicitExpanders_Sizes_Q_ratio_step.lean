-- Prove2me | solution 1 for ExplicitExpanders.Sizes.Q_ratio_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:06:13.869448+00:00
-- url     : https://prove2.me/submissions/51c07da8-0b8c-41e7-a404-28835daee447

import Mathlib
import Definitions.Def_ExplicitExpanders_Sizes_Q



namespace ExplicitExpanders.Sizes

theorem qr_core {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂)
    {μ : ℝ} (hμ : 0 < μ) {k₁ k₂ : ℕ} (hk₁ : 0 < k₁)
    (hlow : 1 ≤ (q₁ : ℝ) ^ k₁ / (q₂ : ℝ) ^ k₂) (hupp : (q₁ : ℝ) ^ k₁ / (q₂ : ℝ) ^ k₂ ≤ 1 + μ)
    {s t : ℕ} (hs : k₁ < s) (ht : 1 ≤ t) :
    1 ≤ (Q q₁ q₂ s t : ℝ) / (Q q₁ q₂ (s - k₁) (t + k₂) : ℝ) ∧
      (Q q₁ q₂ s t : ℝ) / (Q q₁ q₂ (s - k₁) (t + k₂) : ℝ) ≤ (1 + μ) ^ 3 := by
  have h1 : (0:ℝ) < q₁ := by exact_mod_cast hq₁.pos
  have h2 : (0:ℝ) < q₂ := by exact_mod_cast hq₂.pos
  have hA : (0:ℝ) < ((q₁ * (q₁ - 1) * (q₁ + 1) / 2 : ℕ) : ℝ) := by
    have : 0 < q₁ * (q₁ - 1) * (q₁ + 1) / 2 := by
      have := hq₁.two_le
      apply Nat.div_pos _ (by norm_num)
      have : 1 ≤ q₁ - 1 := by omega
      calc 2 ≤ q₁ := ‹2 ≤ q₁›
        _ = q₁ * 1 * 1 := by ring
        _ ≤ q₁ * (q₁ - 1) * (q₁ + 1) := by gcongr <;> omega
    exact_mod_cast this
  have hB : (0:ℝ) < ((q₂ * (q₂ - 1) * (q₂ + 1) / 2 : ℕ) : ℝ) := by
    have : 0 < q₂ * (q₂ - 1) * (q₂ + 1) / 2 := by
      have := hq₂.two_le
      apply Nat.div_pos _ (by norm_num)
      have : 1 ≤ q₂ - 1 := by omega
      calc 2 ≤ q₂ := ‹2 ≤ q₂›
        _ = q₂ * 1 * 1 := by ring
        _ ≤ q₂ * (q₂ - 1) * (q₂ + 1) := by gcongr <;> omega
    exact_mod_cast this
  have key : (Q q₁ q₂ s t : ℝ) / (Q q₁ q₂ (s - k₁) (t + k₂) : ℝ)
      = ((q₁ : ℝ) ^ k₁ / (q₂ : ℝ) ^ k₂) ^ 3 := by
    have e1 : 3 * (s - 1) = 3 * (s - k₁ - 1) + 3 * k₁ := by omega
    have e2 : 3 * (t + k₂ - 1) = 3 * (t - 1) + 3 * k₂ := by omega
    unfold Q
    rw [e1, e2]
    push_cast
    generalize ((q₁ * (q₁ - 1) * (q₁ + 1) / 2 : ℕ) : ℝ) = A at hA ⊢
    generalize ((q₂ * (q₂ - 1) * (q₂ + 1) / 2 : ℕ) : ℝ) = B at hB ⊢
    field_simp
    ring
  rw [key]
  constructor
  · exact one_le_pow₀ hlow
  · exact pow_le_pow_left₀ (by linarith) hupp 3

end ExplicitExpanders.Sizes

open ExplicitExpanders.Sizes


theorem solution {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂)
    {μ : ℝ} (hμ : 0 < μ) {k₁ k₂ : ℕ} (hk₁ : 0 < k₁)
    (hlow : 1 ≤ (q₁ : ℝ) ^ k₁ / (q₂ : ℝ) ^ k₂) (hupp : (q₁ : ℝ) ^ k₁ / (q₂ : ℝ) ^ k₂ ≤ 1 + μ)
    {s t : ℕ} (hs : k₁ < s) (ht : 1 ≤ t) :
    1 ≤ (Q q₁ q₂ s t : ℝ) / (Q q₁ q₂ (s - k₁) (t + k₂) : ℝ) ∧
      (Q q₁ q₂ s t : ℝ) / (Q q₁ q₂ (s - k₁) (t + k₂) : ℝ) ≤ (1 + μ) ^ 3 := by
  exact qr_core hq₁ hq₂ hne hμ hk₁ hlow hupp hs ht
