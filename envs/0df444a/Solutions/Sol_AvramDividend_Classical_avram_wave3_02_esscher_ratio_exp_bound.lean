-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_esscher_ratio_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:34:12.621528+00:00
-- url     : https://prove2.me/submissions/369994f4-8479-438b-bbfe-d58dc25f6b25

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The original q-scale first-upcrossing factor decays exponentially
with the gap between the current capital and a higher barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ φ : ℝ, 0 < φ ∧
      ∀ x a : ℝ, 0 < x → x ≤ a →
        W x / W a ≤ Real.exp (-φ * (a - x)) := by
  obtain ⟨hWpos, φ, hφ, htilt⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  refine ⟨φ, hφ, ?_⟩
  intro x a hx hxa
  have ha : 0 < a := lt_of_lt_of_le hx hxa
  have hWa : 0 < W a := hWpos a ha
  have hle : Real.exp (-φ * x) * W x ≤
      Real.exp (-φ * a) * W a :=
    htilt (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr ha) hxa
  have hxunit :
      W x = Real.exp (φ * x) * (Real.exp (-φ * x) * W x) := by
    rw [← mul_assoc, ← Real.exp_add]
    have heq : φ * x + -φ * x = 0 := by ring
    rw [heq, Real.exp_zero, one_mul]
  have hstep : W x ≤ Real.exp (φ * x) * (Real.exp (-φ * a) * W a) := by
    calc
      W x = Real.exp (φ * x) * (Real.exp (-φ * x) * W x) := hxunit
      _ ≤ Real.exp (φ * x) * (Real.exp (-φ * a) * W a) :=
        mul_le_mul_of_nonneg_left hle (le_of_lt (Real.exp_pos _))
  have hconvert :
      Real.exp (φ * x) * (Real.exp (-φ * a) * W a) =
        Real.exp (-φ * (a - x)) * W a := by
    rw [← mul_assoc, ← Real.exp_add]
    have heq : φ * x + -φ * a = -φ * (a - x) := by ring
    rw [heq]
  have hfinal : W x ≤ Real.exp (-φ * (a - x)) * W a :=
    hstep.trans_eq hconvert
  exact (div_le_iff₀ hWa).2 (by simpa [mul_comm] using hfinal)
