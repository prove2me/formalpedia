-- Prove2me | solution 1 for DeletedPrimes.errExp_argmax
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:05:33.495273+00:00
-- url     : https://prove2.me/submissions/1d8eb367-a233-44b9-998a-e8177b9cd093

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
import Theorems.Thm_DeletedPrimes_hitExp_le_pos
import Theorems.Thm_DeletedPrimes_hitExp_le_neg
import Theorems.Thm_DeletedPrimes_le_hitExp_u
import Theorems.Thm_DeletedPrimes_maxExp_u
import Theorems.Thm_DeletedPrimes_argmaxExp_u

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {α κ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hκ : 0 ≤ κ) :
    errExp k α κ (argmaxExp k α κ) = maxExp k α κ := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  obtain ⟨u, rfl⟩ : ∃ u : ℝ, κ = k * u := ⟨κ / k, by field_simp⟩
  have hu0 : 0 ≤ u := by nlinarith
  have hαu : 0 ≤ α * u := mul_nonneg h0.le hu0
  rw [maxExp_u hk, argmaxExp_u hk]
  unfold errExp
  split_ifs with hα
  · have hH : hitExp k α (k * u) (k * u - α * u) = α * u := by
      apply le_antisymm
      · have h := hitExp_le_pos hk (α := α) (τ := k * u - α * u) rfl (Nat.zero_le k)
          (by push_cast; linarith)
        push_cast at h
        linarith
      · apply le_hitExp_u hk rfl
        intro i hi
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · have := le_max_left ((k : ℝ) * u - (k * u - α * u) - ((0 : ℕ) : ℝ) * u) 0
          simp only [Nat.cast_zero] at this ⊢
          linarith
        · have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hpos
          have := le_max_right ((k : ℝ) * u - (k * u - α * u) - (i : ℝ) * u) 0
          have : 0 ≤ α * u * ((i : ℝ) - 1) := mul_nonneg hαu (by linarith)
          linarith
    rw [hH]; ring
  · push Not at hα
    have hH : hitExp k α (k * u) ((1 - α) * u) = α * k * u := by
      apply le_antisymm
      · have h1u : 0 ≤ (1 - α) * u := mul_nonneg (by linarith) hu0
        exact hitExp_le_neg hk (α := α) (τ := (1 - α) * u) rfl le_rfl (by linarith)
      · apply le_hitExp_u hk rfl
        intro i hi
        rcases Nat.lt_or_ge i k with hlt | hge
        · have hi1 : (i : ℝ) + 1 ≤ k := by exact_mod_cast hlt
          have := le_max_left ((k : ℝ) * u - (1 - α) * u - (i : ℝ) * u) 0
          have : 0 ≤ (1 - α) * ((k : ℝ) - 1 - i) * u :=
            mul_nonneg (mul_nonneg (by linarith) (by linarith)) hu0
          linarith
        · have hik : i = k := le_antisymm hi hge
          subst hik
          have := le_max_right ((i : ℝ) * u - (1 - α) * u - (i : ℝ) * u) 0
          linarith
    rw [hH]; ring
end DeletedPrimes
