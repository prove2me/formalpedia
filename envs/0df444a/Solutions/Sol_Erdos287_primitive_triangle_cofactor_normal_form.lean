-- Prove2me | solution 1 for Erdos287.primitive_triangle_cofactor_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:05:47.134206+00:00
-- url     : https://prove2.me/submissions/7fa9d79a-b209-4497-84ed-0c5a09c36c9f

import Mathlib

set_option autoImplicit false

private theorem pair_gcd_coprime (a b c : ℕ) (h : Nat.gcd (Nat.gcd a b) c = 1) :
    (Nat.gcd a b).Coprime (Nat.gcd a c) := by
  change Nat.gcd (Nat.gcd a b) (Nat.gcd a c) = 1
  apply Nat.dvd_one.mp
  rw [← h]
  exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right a c))

/-- The three pairwise adjacencies of a primitive affine triangle
give an additive relation after its pairwise gcds are removed. -/
theorem solution (s₁ s₂ s₃ : ℕ) (r₁ r₂ r₃ : ℤ)
    (h₁ : 0 < s₁) (h₂ : 0 < s₂) (h₃ : 0 < s₃)
    (hprim : Nat.gcd (Nat.gcd s₁ s₂) s₃ = 1)
    (h₁₂ : (s₂ : ℤ) * r₁ - (s₁ : ℤ) * r₂ = ↑(Nat.gcd s₁ s₂))
    (h₂₃ : (s₃ : ℤ) * r₂ - (s₂ : ℤ) * r₃ = ↑(Nat.gcd s₂ s₃))
    (h₁₃ : (s₃ : ℤ) * r₁ - (s₁ : ℤ) * r₃ = ↑(Nat.gcd s₁ s₃)) :
    let g₁₂ := Nat.gcd s₁ s₂
    let g₁₃ := Nat.gcd s₁ s₃
    let g₂₃ := Nat.gcd s₂ s₃
    ∃ (u₁ u₂ u₃ : ℕ), 0 < u₁ ∧ 0 < u₂ ∧ 0 < u₃ ∧
      s₁ = g₁₂ * g₁₃ * u₁ ∧ s₂ = g₁₂ * g₂₃ * u₂ ∧ s₃ = g₁₃ * g₂₃ * u₃ ∧
      u₂ = u₁ + u₃ ∧
      Nat.lcm s₁ s₂ = g₁₂ * g₁₃ * g₂₃ * (u₁ * u₂) ∧
      Nat.lcm s₁ s₃ = g₁₂ * g₁₃ * g₂₃ * (u₁ * u₃) ∧
      Nat.lcm s₂ s₃ = g₁₂ * g₁₃ * g₂₃ * (u₂ * u₃) := by
  intro g₁₂ g₁₃ g₂₃
  have hcop₁ : g₁₂.Coprime g₁₃ := pair_gcd_coprime s₁ s₂ s₃ hprim
  have hcop₂ : g₁₂.Coprime g₂₃ := by
    simpa only [g₁₂, g₂₃, Nat.gcd_comm s₂ s₁] using
      pair_gcd_coprime s₂ s₁ s₃ (by simpa only [Nat.gcd_comm s₂ s₁] using hprim)
  have hcop₃ : g₁₃.Coprime g₂₃ := by
    simpa only [g₁₃, g₂₃, Nat.gcd_comm s₃ s₁, Nat.gcd_comm s₃ s₂] using
      pair_gcd_coprime s₃ s₁ s₂ (by
        calc
          Nat.gcd (Nat.gcd s₃ s₁) s₂ = Nat.gcd s₃ (Nat.gcd s₁ s₂) := Nat.gcd_assoc _ _ _
          _ = _ := by rw [Nat.gcd_comm, hprim])
  have hp₁₂ : 0 < g₁₂ := Nat.gcd_pos_of_pos_left _ h₁
  have hp₁₃ : 0 < g₁₃ := Nat.gcd_pos_of_pos_left _ h₁
  have hp₂₃ : 0 < g₂₃ := Nat.gcd_pos_of_pos_left _ h₂
  have hd₁ : g₁₂ * g₁₃ ∣ s₁ := hcop₁.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
  have hd₂ : g₁₂ * g₂₃ ∣ s₂ := hcop₂.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  have hd₃ : g₁₃ * g₂₃ ∣ s₃ := hcop₃.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
  obtain ⟨u₁, hu₁⟩ := hd₁
  obtain ⟨u₂, hu₂⟩ := hd₂
  obtain ⟨u₃, hu₃⟩ := hd₃
  have hu₁' : 0 < u₁ := by
    apply Nat.pos_of_ne_zero
    intro hn
    simp [hn] at hu₁
    omega
  have hu₂' : 0 < u₂ := by
    apply Nat.pos_of_ne_zero
    intro hn
    simp [hn] at hu₂
    omega
  have hu₃' : 0 < u₃ := by
    apply Nat.pos_of_ne_zero
    intro hn
    simp [hn] at hu₃
    omega
  have hdet : g₁₃ * s₂ = g₁₂ * s₃ + g₂₃ * s₁ := by
    have he : (g₁₃ : ℤ) * s₂ = (g₁₂ : ℤ) * s₃ + (g₂₃ : ℤ) * s₁ := by
      linear_combination (s₃ : ℤ) * h₁₂ + (s₁ : ℤ) * h₂₃ - (s₂ : ℤ) * h₁₃
    exact_mod_cast he
  refine ⟨u₁, u₂, u₃, hu₁', hu₂', hu₃', hu₁, hu₂, hu₃, ?_, ?_, ?_, ?_⟩
  · apply Nat.eq_of_mul_eq_mul_left (mul_pos (mul_pos hp₁₂ hp₁₃) hp₂₃)
    calc
      g₁₂ * g₁₃ * g₂₃ * u₂ = g₁₃ * s₂ := by rw [hu₂]; ring
      _ = g₁₂ * s₃ + g₂₃ * s₁ := hdet
      _ = _ := by rw [hu₁, hu₃]; ring
  · apply Nat.eq_of_mul_eq_mul_left hp₁₂
    calc
      g₁₂ * Nat.lcm s₁ s₂ = s₁ * s₂ := Nat.gcd_mul_lcm _ _
      _ = _ := by rw [hu₁, hu₂]; ring
  · apply Nat.eq_of_mul_eq_mul_left hp₁₃
    calc
      g₁₃ * Nat.lcm s₁ s₃ = s₁ * s₃ := Nat.gcd_mul_lcm _ _
      _ = _ := by rw [hu₁, hu₃]; ring
  · apply Nat.eq_of_mul_eq_mul_left hp₂₃
    calc
      g₂₃ * Nat.lcm s₂ s₃ = s₂ * s₃ := Nat.gcd_mul_lcm _ _
      _ = _ := by rw [hu₂, hu₃]; ring

