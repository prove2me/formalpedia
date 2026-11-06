-- Prove2me | solution 1 for BianchiIX.curveSampleStep_samples
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:31:12.11749+00:00
-- url     : https://prove2.me/submissions/f95a93a3-97a3-4ebd-9fb9-5c733e174732

import Definitions.Def_BianchiIX_Analysis_CurveMeasurability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology


theorem solution {l r x : ℝ} (hlr : l < r) (hx : x ∈ Icc l r) (n : ℕ) :
    curveSampleStep l r x n ≠ 0 ∧
      x + curveSampleStep l r x n ∈ Ioo l r ∧
      x + 2 * curveSampleStep l r x n ∈ Ioo l r := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : 0 < 3 * ((n : ℝ) + 1) := by positivity
  unfold curveSampleStep
  by_cases hxr : x < r
  · rw [if_pos hxr]
    have hp : 0 < (r - x) / (3 * ((n : ℝ) + 1)) := div_pos (sub_pos.mpr hxr) hden
    have hb : 2 * ((r - x) / (3 * ((n : ℝ) + 1))) < r - x := by
      rw [← mul_div_assoc, div_lt_iff₀ hden]
      nlinarith
    exact ⟨ne_of_gt hp, ⟨by linarith [hx.1], by linarith⟩,
      ⟨by linarith [hx.1], by linarith⟩⟩
  · rw [if_neg hxr]
    have hxe : x = r := le_antisymm hx.2 (le_of_not_gt hxr)
    have hp : (l - x) / (3 * ((n : ℝ) + 1)) < 0 :=
      div_neg_of_neg_of_pos (by linarith) hden
    have hb : l - x < 2 * ((l - x) / (3 * ((n : ℝ) + 1))) := by
      rw [← mul_div_assoc, lt_div_iff₀ hden]
      nlinarith
    exact ⟨ne_of_lt hp, ⟨by linarith, by linarith [hx.2]⟩,
      ⟨by linarith, by linarith [hx.2]⟩⟩
