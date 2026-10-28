-- Prove2me | solution 1 for AvramDividend.Classical.bv_dyadic_slope_to_positive_right_germ_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:11:50.771807+00:00
-- url     : https://prove2.me/submissions/a6f1704b-b31e-4c0c-b230-83b3c033641d

import Mathlib
open Filter Topology

theorem solution
    (S : NNReal → ℝ) (δ : ℕ → NNReal) (d : ℝ)
    (hd : 0 < d) (hδpos : ∀ n, 0 < δ n)
    (hMon : Monotone S)
    (hRatio : ∀ n, (δ n : ℝ) ≤ 2 * (δ (n + 1) : ℝ))
    (hCover : ∀ (N : ℕ) (t : NNReal), 0 < t → t < δ N →
      ∃ n : ℕ, N ≤ n ∧ δ (n + 1) ≤ t ∧ t ≤ δ n)
    (hSlope : Tendsto (fun n : ℕ => S (δ n) / (δ n : ℝ))
      atTop (𝓝 (0 : ℝ))) :
    ∃ ε : NNReal, 0 < ε ∧
      ∀ t : NNReal, 0 < t → t < ε → 0 < d * (t : ℝ) - S t := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hSlope).2 (d / 2) (by linarith))
  refine ⟨δ N, hδpos N, fun t ht htN => ?_⟩
  obtain ⟨n, hn, h1, h2⟩ := hCover N t ht htN
  have hpos : (0 : ℝ) < δ n := by exact_mod_cast hδpos n
  have hr := hN n hn
  rw [div_lt_iff₀ hpos] at hr
  have hSt : S t ≤ S (δ n) := hMon h2
  have h1' : (δ (n + 1) : ℝ) ≤ t := by exact_mod_cast h1
  nlinarith [hRatio n]
