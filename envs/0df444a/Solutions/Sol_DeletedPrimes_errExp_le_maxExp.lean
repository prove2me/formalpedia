-- Prove2me | solution 1 for DeletedPrimes.errExp_le_maxExp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:03:43.682803+00:00
-- url     : https://prove2.me/submissions/03fb9f31-8be7-4b94-9f2d-8fc2b91a6409

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
import Theorems.Thm_DeletedPrimes_hitExp_le_pos
import Theorems.Thm_DeletedPrimes_hitExp_le_neg
import Theorems.Thm_DeletedPrimes_decomp
import Theorems.Thm_DeletedPrimes_maxExp_u

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {α κ τ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hκ : 0 ≤ κ)
    (hτ0 : 0 ≤ τ) (hτκ : τ ≤ κ) : errExp k α κ τ ≤ maxExp k α κ := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  obtain ⟨u, rfl⟩ : ∃ u : ℝ, κ = k * u := ⟨κ / k, by field_simp⟩
  have hu0 : 0 ≤ u := by nlinarith
  rw [maxExp_u hk]
  unfold errExp
  obtain ⟨n, hnk, hnu, hcase⟩ :=
    decomp h0 hu0 (sub_nonneg.2 hτκ) (by linarith : (k : ℝ) * u - τ ≤ k * u)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnk' : (n : ℝ) ≤ k := by exact_mod_cast hnk
  split_ifs with hα
  · rcases hcase with hA | ⟨hB1, hB2, hB3⟩
    · have hH := hitExp_le_pos hk (α := α) (τ := τ) rfl hnk (by linarith)
      have e1 : α * (k * u - τ - n * u) ≤ α * (α * u) := mul_le_mul_of_nonneg_left hA h0.le
      have e2 : 0 ≤ (1 - 2 * α) * n * u := mul_nonneg (mul_nonneg (by linarith) hn0) hu0
      linarith
    · have hH := hitExp_le_neg hk (α := α) (τ := τ) rfl (i := n + 1) hB3 (by push_cast; linarith)
      push_cast at hH
      have e1 : (1 - α) * (α * u) ≤ (1 - α) * (k * u - τ - n * u) :=
        mul_le_mul_of_nonneg_left hB1.le (by linarith)
      have e2 : 0 ≤ (1 - 2 * α) * n * u := mul_nonneg (mul_nonneg (by linarith) hn0) hu0
      linarith
  · push Not at hα
    rcases hcase with hA | ⟨hB1, hB2, hB3⟩
    · rcases Nat.lt_or_ge n k with hlt | hge
      · have hH := hitExp_le_pos hk (α := α) (τ := τ) rfl hnk (by linarith)
        have hn1 : (n : ℝ) + 1 ≤ k := by exact_mod_cast hlt
        have e1 : α * (k * u - τ - n * u) ≤ α * (α * u) := mul_le_mul_of_nonneg_left hA h0.le
        have e2 : 0 ≤ (2 * α - 1) * (k - n - 1) * u :=
          mul_nonneg (mul_nonneg (by linarith) (by linarith)) hu0
        linarith
      · have hnk2 : n = k := le_antisymm hnk hge
        subst hnk2
        have hτ' : τ = 0 := by linarith
        subst hτ'
        have hH := hitExp_le_pos hk (α := α) (τ := 0) rfl hnk (by linarith)
        have e : 0 ≤ (1 - α) ^ 2 * u := mul_nonneg (sq_nonneg _) hu0
        linarith
    · have hH := hitExp_le_neg hk (α := α) (τ := τ) rfl (i := n + 1) hB3 (by push_cast; linarith)
      push_cast at hH
      have hn1 : (n : ℝ) + 1 ≤ k := by exact_mod_cast hB3
      have e1 : (1 - α) * (α * u) ≤ (1 - α) * (k * u - τ - n * u) :=
        mul_le_mul_of_nonneg_left hB1.le (by linarith)
      have e2 : 0 ≤ (2 * α - 1) * (k - n - 1) * u :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) hu0
      linarith
end DeletedPrimes
