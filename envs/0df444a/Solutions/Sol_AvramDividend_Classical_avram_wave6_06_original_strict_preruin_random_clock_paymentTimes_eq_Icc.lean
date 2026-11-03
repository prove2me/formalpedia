-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_strict_preruin_random_clock_paymentTimes_eq_Icc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:56:56.756304+00:00
-- url     : https://prove2.me/submissions/fec6a2f6-a344-4690-bf01-3bb2538ae8c6

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
/-- A strictly pre-ruin source clock has exactly the genuine original
    payment domain [0,τ], including the right dividend atom at time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (τ : Ω → ℝ≥0)
    (hStrict : (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ) =
      Icc (0 : ℝ) (τ ω : ℝ) := by
  have hσ : (0 : ℝ≥0∞) < ruinTime X x D ω :=
    lt_of_le_of_lt bot_le hStrict
  rw [paymentTimes_eq_strict_of_pos (ruinTime X x D ω) hσ]
  ext t
  simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨ht0, _⟩, htτ⟩
    exact ⟨ht0, htτ⟩
  · rintro ⟨ht0, htτ⟩
    refine ⟨⟨ht0, ?_⟩, htτ⟩
    have hle : ENNReal.ofReal t ≤ (τ ω : ℝ≥0∞) := by
      simpa using (ENNReal.ofReal_le_ofReal htτ)
    exact lt_of_le_of_lt hle hStrict
