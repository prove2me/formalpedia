-- Prove2me | solution 1 for AvramDividend.Classical.renewal_quotient_le_of_finite_cycle_bounds
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-24T11:36:11.308406+00:00
-- url     : https://prove2.me/submissions/9326c450-8b2b-4468-afe8-5849866d4001

import Mathlib

open Filter Topology
open scoped ENNReal

theorem solution : ¬ (∀ (V : ℝ≥0∞) (W : ℝ → ℝ) (a d : ℝ)
    (hD : HasDerivAt W d a) (hd : d ≠ 0)
    (hWa : 0 < W a)
    (hW8 : ∀ ε : ℝ, 0 < ε → ε < a → 0 ≤ W (a - ε))
    (hlt : ∀ ε : ℝ, 0 < ε → ε < a → W (a - ε) < W a)
    (hfin : ∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < a →
      ∑ k ∈ Finset.range N,
        ENNReal.ofReal ε * (ENNReal.ofReal (W (a - ε) / W a)) ^ (k + 1) ≤ V),
    ENNReal.ofReal (W a / d) ≤ V) := by
  intro H
  have hD : HasDerivAt (fun x : ℝ => x + 1) 1 0 := (hasDerivAt_id 0).add_const 1
  have := H 0 (fun x => x + 1) 0 1 hD one_ne_zero (by norm_num)
    (fun ε h1 h2 => absurd (h1.trans h2) (lt_irrefl _))
    (fun ε h1 h2 => absurd (h1.trans h2) (lt_irrefl _))
    (fun N ε h1 h2 => absurd (h1.trans h2) (lt_irrefl _))
  norm_num at this
