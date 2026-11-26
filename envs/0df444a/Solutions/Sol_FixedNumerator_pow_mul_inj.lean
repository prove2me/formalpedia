-- Prove2me | solution 1 for FixedNumerator.pow_mul_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:41:30.696175+00:00
-- url     : https://prove2.me/submissions/e9b6fd30-d007-4eb7-8ad3-05efcde5aa42

module
public import Definitions.Def_FixedNumerator_Local
public import Definitions.Def_FixedNumerator_Split

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution {π a b : GaussianInt} (hπ : Prime π) (ha : ¬ π ∣ a) (hb : ¬ π ∣ b) {k j : ℕ}
    (h : π ^ k * a = π ^ j * b) : k = j ∧ a = b := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  rcases lt_trichotomy k j with hkj | hkj | hkj
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkj
    have : a = π ^ (d + 1) * b := by
      apply mul_left_cancel₀ (pow_ne_zero k hπ0)
      rw [h]; ring
    exact ha ⟨π ^ d * b, by rw [this]; ring⟩
  · subst hkj; exact ⟨rfl, mul_left_cancel₀ (pow_ne_zero k hπ0) h⟩
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkj
    have : b = π ^ (d + 1) * a := by
      apply mul_left_cancel₀ (pow_ne_zero j hπ0)
      rw [← h]; ring
    exact hb ⟨π ^ d * a, by rw [this]; ring⟩
end FixedNumerator
