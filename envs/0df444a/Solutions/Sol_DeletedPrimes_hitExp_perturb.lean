-- Prove2me | solution 1 for DeletedPrimes.hitExp_perturb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:16:08.56846+00:00
-- url     : https://prove2.me/submissions/90ce036f-bcef-496e-8678-d1e449b8abe7

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} {α κ τ δ : ℝ} (h0 : 0 ≤ α) (hκ : 0 ≤ κ) (s : ℕ → ℝ)
    (hs : ∀ i ≤ k, |s i - i / k| ≤ δ) :
    (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one
        (fun i => α * κ * s i + max (κ - τ - κ * s i) 0)
      ≤ hitExp k α κ τ + (1 + α) * κ * δ := by
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' (Finset.nonempty_range_add_one (n := k))
    (fun i : ℕ => α * κ * i / k + max (κ - τ - κ * i / k) 0)
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hH : hitExp k α κ τ = α * κ * j / k + max (κ - τ - κ * j / k) 0 := hjeq
  rw [hH]
  refine le_trans (Finset.inf'_le _ hj) ?_
  obtain ⟨hl, hr⟩ := abs_le.1 (hs j hjk)
  rw [show α * κ * (j : ℝ) / k = α * κ * ((j : ℝ) / k) by ring,
    show κ * (j : ℝ) / k = κ * ((j : ℝ) / k) by ring]
  generalize (j : ℝ) / k = q at hl hr ⊢
  have hδ : 0 ≤ δ := by linarith
  have m1 : max (κ - τ - κ * s j) 0 ≤ max (κ - τ - κ * q) 0 + κ * δ := by
    apply max_le
    · have := le_max_left (κ - τ - κ * q) 0
      have : κ * (q - s j) ≤ κ * δ := mul_le_mul_of_nonneg_left (by linarith) hκ
      linarith
    · have := le_max_right (κ - τ - κ * q) 0
      have : 0 ≤ κ * δ := mul_nonneg hκ hδ
      linarith
  have m2 : α * κ * s j ≤ α * κ * q + α * κ * δ := by
    have := mul_le_mul_of_nonneg_left (show s j - q ≤ δ by linarith) (mul_nonneg h0 hκ)
    linarith
  linarith
end DeletedPrimes
