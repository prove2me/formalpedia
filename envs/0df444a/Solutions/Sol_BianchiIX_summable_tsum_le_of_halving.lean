-- Prove2me | solution 1 for BianchiIX.summable_tsum_le_of_halving
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:04:57.752449+00:00
-- url     : https://prove2.me/submissions/f355e87c-e970-4925-b319-8c68a159af1e

import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open BianchiIX
open Filter
open scoped Topology


/-- A nonnegative sequence with one-step contraction has a quantitative sum. -/
theorem solution {u : ℕ → ℝ} (hu : ∀ m, 0 ≤ u m)
    (hstep : ∀ m, u (m + 1) ≤ (1 / 2) * u m) :
    Summable u ∧ (∑' m, u m) ≤ 2 * u 0 := by
  have hbound : ∀ m, u m ≤ (1 / 2 : ℝ) ^ m * u 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc
        u (m + 1) ≤ (1 / 2) * u m := hstep m
        _ ≤ (1 / 2) * ((1 / 2 : ℝ) ^ m * u 0) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2 : ℝ) ^ (m + 1) * u 0 := by rw [pow_succ]; ring
  have hgeom := summable_geometric_two.mul_right (u 0)
  have hs : Summable u := Summable.of_nonneg_of_le hu hbound hgeom
  refine ⟨hs, (hs.tsum_le_tsum hbound hgeom).trans_eq ?_⟩
  rw [tsum_mul_right, tsum_geometric_two]
