-- Prove2me | solution 1 for DataDrivenNV.WMS.lemma2_exponential_envelope
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:36:54.849615+00:00
-- url     : https://prove2.me/submissions/d7c18174-8e06-465f-a679-b7bdb00680c4

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_DataDrivenNV_WMS_Setting

set_option autoImplicit false
open MeasureTheory DataDrivenNV.WMS

theorem solution (f : ℝ → ℝ) (hf : IsPdf f)
    (hlc : ConvexOptimization.LogConcaveOn Set.univ f)
    (t γ₀ γ₁ : ℝ) (hγ₀ : 0 < γ₀) (hft : f t = γ₀) (hsg : IsLogSupergradient f t γ₁) :
    ∀ x, f x ≤ γ₀ * Real.exp (γ₁ * (x - t)) := by
  intro x
  rcases (hf.2.1 x).eq_or_lt with h | h
  · rw [← h]; positivity
  · have h2 := hsg x h
    rw [hft] at h2
    calc f x = Real.exp (Real.log (f x)) := (Real.exp_log h).symm
      _ ≤ Real.exp (Real.log γ₀ + γ₁ * (x - t)) := Real.exp_le_exp.mpr h2
      _ = γ₀ * Real.exp (γ₁ * (x - t)) := by rw [Real.exp_add, Real.exp_log hγ₀]
