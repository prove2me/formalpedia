-- Prove2me | solution 1 for FeynmanKac.discount_pos_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:32:17.482686+00:00
-- url     : https://prove2.me/submissions/f32b3798-8c8a-44ab-b951-aecc9ab3abbb

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A nonnegative killing rate keeps its exponential discount in (0, 1]. -/
theorem solution {Ω : Type*} (X : ℝ → Ω → ℝ) (V : ℝ → ℝ → ℝ)
    (t s : ℝ) (hts : t ≤ s) (ω : Ω)
    (hV : ∀ r ∈ Set.Icc t s, 0 ≤ V (X r ω) r)
    (hInt : IntervalIntegrable (fun r => V (X r ω) r) MeasureTheory.volume t s) :
    0 < Real.exp (-(∫ r in t..s, V (X r ω) r)) ∧
    Real.exp (-(∫ r in t..s, V (X r ω) r)) ≤ 1 := by
  have hnonneg : 0 ≤ ∫ r in t..s, V (X r ω) r := by
    apply intervalIntegral.integral_nonneg hts
    intro r hr
    exact hV r hr
  refine ⟨Real.exp_pos _, ?_⟩
  calc
    Real.exp (-(∫ r in t..s, V (X r ω) r)) ≤ Real.exp 0 := by
      apply Real.exp_le_exp_of_le
      exact neg_nonpos.mpr hnonneg
    _ = 1 := Real.exp_zero
