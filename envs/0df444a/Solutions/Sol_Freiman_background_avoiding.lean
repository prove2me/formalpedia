-- Prove2me | solution 1 for Freiman.background_avoiding
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:29:41.915654+00:00
-- url     : https://prove2.me/submissions/15186431-ad58-46d0-9777-1fea532b5ed1

import Theorems.Thm_Freiman_background_restricted
import Theorems.Thm_Freiman_background_three_avoids_four_pairs

open Freiman

theorem solution (a : ℤ → ℕ+) (ha : ∀ i : ℤ, (a i : ℕ) ≤ 3)
    (havoid : AvoidsBlock a [3,1,3,1,3]) (i : ℤ) :
    localValue a i ≤ 4 * Real.sqrt 462 / 19 := by
  obtain ⟨h14, h41⟩ := background_three_avoids_four_pairs a ha
  exact background_restricted a (fun j => (ha j).trans (by decide)) h14 h41 havoid i (ha i)

