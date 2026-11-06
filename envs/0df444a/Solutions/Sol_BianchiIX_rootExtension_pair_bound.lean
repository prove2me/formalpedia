-- Prove2me | solution 1 for BianchiIX.rootExtension_pair_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:48:25.516444+00:00
-- url     : https://prove2.me/submissions/e5c471f8-d2fc-4761-8a0e-02a2d2dc78f0

import Definitions.Def_BianchiIX_Analysis_RootExtension
import Theorems.Thm_BianchiIX_rootExtension_bounds
import Theorems.Thm_BianchiIX_rootExtension_pos
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter MeasureTheory
open scoped Topology
open BianchiIX
noncomputable section


theorem solution {s t d c e x θ B : ℝ} (hs : 0 < s) (ht : 0 < t)
    (he : |e| = 1) (hx : 0 ≤ e * x) (hd : |d| ≤ θ / 2) (hc : |c| ≤ θ / 2)
    (hθ : θ ≤ 1) (hB : s ^ 2 + t ^ 2 ≤ B) :
    rootExtension s d e x ^ 2 + rootExtension t c e x ^ 2 ≤ (1 + θ / 4) ^ 2 * B := by
  have hs2 := pow_le_pow_left₀ (rootExtension_pos hs he hx hd hθ).le
    (rootExtension_bounds hs he hx hd).2 2
  have ht2 := pow_le_pow_left₀ (rootExtension_pos ht he hx hc hθ).le
    (rootExtension_bounds ht he hx hc).2 2
  calc
    _ ≤ ((1 + θ / 4) * s) ^ 2 + ((1 + θ / 4) * t) ^ 2 := add_le_add hs2 ht2
    _ = (1 + θ / 4) ^ 2 * (s ^ 2 + t ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
