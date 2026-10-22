-- Prove2me | solution 1 for BellDetEff.TwoParty.eqs_8_11_inconsistent
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:36:00.755867+00:00
-- url     : https://prove2.me/submissions/05bfa9fd-6176-48a1-973d-862184d1f87f

import Mathlib
set_option autoImplicit false

theorem solution (P : ℕ) [Fact P.Prime] (x₁ x₂ y₁ y₂ : ℕ)
    (hx₁ : 1 ≤ x₁) (hx₁P : x₁ ≤ P) (hx₂ : 1 ≤ x₂) (hx₂P : x₂ ≤ P)
    (hy₁ : 1 ≤ y₁) (hy₁P : y₁ ≤ P) (hy₂ : 1 ≤ y₂) (hy₂P : y₂ ≤ P)
    (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂) (a₁ a₂ b₁ b₂ : ZMod P) :
    ¬ (a₁ + b₁ = (x₁ : ZMod P) * y₁ ∧ a₁ + b₂ = (x₁ : ZMod P) * y₂ ∧
        a₂ + b₁ = (x₂ : ZMod P) * y₁ ∧ a₂ + b₂ = (x₂ : ZMod P) * y₂) := by
  rintro ⟨h1, h2, h3, h4⟩
  have key : ∀ u v : ℕ, 1 ≤ u → u ≤ P → 1 ≤ v → v ≤ P → u ≠ v → (u : ZMod P) ≠ (v : ZMod P) := by
    intro u v hu huP hv hvP huv h
    rw [ZMod.natCast_eq_natCast_iff'] at h
    rcases eq_or_lt_of_le huP with rfl | hu'
    · rcases eq_or_lt_of_le hvP with rfl | hv'
      · exact huv rfl
      · rw [Nat.mod_self, Nat.mod_eq_of_lt hv'] at h
        omega
    · rcases eq_or_lt_of_le hvP with rfl | hv'
      · rw [Nat.mod_self, Nat.mod_eq_of_lt hu'] at h
        omega
      · rw [Nat.mod_eq_of_lt hu', Nat.mod_eq_of_lt hv'] at h
        exact huv h
  have hxne := key x₁ x₂ hx₁ hx₁P hx₂ hx₂P hx
  have hyne := key y₁ y₂ hy₁ hy₁P hy₂ hy₂P hy
  have : ((x₁ : ZMod P) - x₂) * ((y₁ : ZMod P) - y₂) = 0 := by
    linear_combination -(h1) + h2 + h3 - h4
  rcases mul_eq_zero.mp this with h | h
  · exact hxne (sub_eq_zero.mp h)
  · exact hyne (sub_eq_zero.mp h)
