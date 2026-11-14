-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB226_exponential_discount_nested_clipping_squared_strip_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:08:18.353422+00:00
-- url     : https://prove2.me/submissions/48a9e13d-581f-42ce-baf0-e5ec33748b68

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Theorems.Thm_AvramDividend_Classical_avram_gbB224_discounted_nested_clipped_gradient_squared_strip_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

/-- Exponential physical-time discount is a contraction for squared clipping errors. -/
theorem solution
    (w : ℝ → ℝ) (a a' b' b B q t : ℝ)
    (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b)
    (hB : 1 ≤ B)
    (hgrad : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ B)
    (hq : 0 ≤ q) (ht : 0 ≤ t) (y : ℝ) :
    (Real.exp (-(q * t)) *
        (if y ∈ Set.Icc a b then deriv w y else 1) -
      Real.exp (-(q * t)) *
        (if y ∈ Set.Icc a' b' then deriv w y else 1))^2 ≤
      4 * B^2 *
        (if y ∈ Set.Icc a a' ∨ y ∈ Set.Icc b' b then (1 : ℝ) else 0) := by
  have hqt : 0 ≤ q * t := mul_nonneg hq ht
  have hExp0 : 0 ≤ Real.exp (-(q * t)) :=
    (Real.exp_pos _).le
  have hExp1 : Real.exp (-(q * t)) ≤ 1 :=
    (Real.exp_le_one_iff).2 (neg_nonpos.mpr hqt)
  exact avram_gbB224_discounted_nested_clipped_gradient_squared_strip_bound
    w a a' b' b B (Real.exp (-(q * t)))
    ha hab hb hB hgrad hExp0 hExp1 y
