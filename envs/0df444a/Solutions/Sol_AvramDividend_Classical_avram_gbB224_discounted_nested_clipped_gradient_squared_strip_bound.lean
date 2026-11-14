-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB224_discounted_nested_clipped_gradient_squared_strip_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:04:18.37258+00:00
-- url     : https://prove2.me/submissions/94d466ce-cbd0-450a-9897-0cbad8e87ced

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Theorems.Thm_AvramDividend_Classical_avram_gbB222_nested_clipping_difference_squared_strip_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

/-- Contractive discount preserves the squared clipping error strip bound. -/
theorem solution
    (w : ℝ → ℝ) (a a' b' b B d : ℝ)
    (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b)
    (hB : 1 ≤ B)
    (hgrad : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ B)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (y : ℝ) :
    (d * (if y ∈ Set.Icc a b then deriv w y else 1) -
      d * (if y ∈ Set.Icc a' b' then deriv w y else 1))^2 ≤
      4 * B^2 *
        (if y ∈ Set.Icc a a' ∨ y ∈ Set.Icc b' b then (1 : ℝ) else 0) := by
  let u : ℝ := if y ∈ Set.Icc a b then deriv w y else 1
  let v : ℝ := if y ∈ Set.Icc a' b' then deriv w y else 1
  have hsq : d ^ 2 ≤ (1 : ℝ) := by
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hd1)]
  have hnonneg : 0 ≤ (u - v) ^ 2 := sq_nonneg _
  have hmul : 0 ≤ (1 - d ^ 2) * (u - v) ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hsq) hnonneg
  have hclip : (u - v) ^ 2 ≤
      4 * B ^ 2 *
      (if y ∈ Set.Icc a a' ∨ y ∈ Set.Icc b' b then (1 : ℝ) else 0) := by
    simpa only [u, v] using
      (avram_gbB222_nested_clipping_difference_squared_strip_bound
        w a a' b' b B ha hab hb hB hgrad y)
  change (d * u - d * v) ^ 2 ≤ _
  calc
    (d * u - d * v) ^ 2 = d ^ 2 * (u - v) ^ 2 := by ring
    _ ≤ (u - v) ^ 2 := by nlinarith
    _ ≤ _ := hclip

