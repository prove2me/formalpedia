-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb75_masked_true_generator_uniform_grid_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:33:14.158333+00:00
-- url     : https://prove2.me/submissions/ea4f5cde-a713-4d00-9950-fa75da31931e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} (q : ℝ) (w g : ℝ → ℝ) (C : ℝ≥0∞)
    (hgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      g y - q * w y ≤ 0)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (Z : ℕ → Ω → ℕ → ℝ) (M : ℕ → Ω → ℕ → Prop) :
    ∀ n : ℕ, ∀ ω : Ω,
      (∑ i ∈ Finset.range (n + 1),
        if M n ω i ∧ 0 < Z n ω i ∧ ENNReal.ofReal (Z n ω i) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (g (Z n ω i) - q * w (Z n ω i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) ≤ 0  := by
  intro n ω
  apply Finset.sum_nonpos
  intro i hi
  split_ifs with h
  · have hidx : i < n + 1 := Finset.mem_range.mp hi
    have hstep : (u n i : ℝ) ≤ (u n (i + 1) : ℝ) := by
      exact_mod_cast hmono n i hidx
    have hwidth : 0 ≤ (u n (i + 1) : ℝ) - (u n i : ℝ) :=
      sub_nonneg.mpr hstep
    have hgenerator : g (Z n ω i) - q * w (Z n ω i) ≤ 0 :=
      hgen (Z n ω i) h.2.1 h.2.2
    have hdisc : 0 ≤ Real.exp (-(q * (u n i : ℝ))) :=
      le_of_lt (Real.exp_pos _)
    have hsource := mul_nonpos_of_nonneg_of_nonpos hdisc hgenerator
    exact mul_nonpos_of_nonpos_of_nonneg hsource hwidth
  · exact le_refl 0
