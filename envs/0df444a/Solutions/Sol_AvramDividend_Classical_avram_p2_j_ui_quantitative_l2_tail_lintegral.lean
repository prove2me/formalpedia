-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_quantitative_l2_tail_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:35:34.071206+00:00
-- url     : https://prove2.me/submissions/ad501b52-e639-45f0-8ba1-de3a0bfbe4ad

import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-! A direct second-moment inequality controls nonnegative L¹ tails. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (V : Ω → ENNReal) (hV : Measurable V)
    (R : ℝ≥0) (hR : 0 < R) (K : ENNReal)
    (hK : (∫⁻ ω, (V ω) ^ (2 : ℕ) ∂P) ≤ K) :
    (R : ENNReal) * (∫⁻ ω,
      (if (R : ENNReal) ≤ V ω then V ω else 0) ∂P) ≤ K := by
  have hm : Measurable
      (fun ω => if (R : ENNReal) ≤ V ω then V ω else 0) := by
    exact hV.ite (measurableSet_le measurable_const hV) measurable_const
  have hpoint : ∀ ω,
      (R : ENNReal) * (if (R : ENNReal) ≤ V ω then V ω else 0) ≤
        (V ω) ^ (2 : ℕ) := by
    intro ω
    by_cases h : (R : ENNReal) ≤ V ω
    · simp only [if_pos h]
      calc
        (R : ENNReal) * V ω ≤ V ω * V ω := by
          gcongr
        _ = (V ω) ^ (2 : ℕ) := by ring
    · simp [h]
  calc
    (R : ENNReal) * (∫⁻ ω,
      (if (R : ENNReal) ≤ V ω then V ω else 0) ∂P) =
      (∫⁻ ω, (R : ENNReal) *
        (if (R : ENNReal) ≤ V ω then V ω else 0) ∂P) := by
          exact (lintegral_const_mul (R : ENNReal) hm).symm
    _ ≤ (∫⁻ ω, (V ω) ^ (2 : ℕ) ∂P) := lintegral_mono hpoint
    _ ≤ K := hK
