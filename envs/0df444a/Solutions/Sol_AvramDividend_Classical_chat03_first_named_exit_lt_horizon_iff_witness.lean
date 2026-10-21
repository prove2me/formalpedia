-- Prove2me | solution 1 for AvramDividend.Classical.chat03_first_named_exit_lt_horizon_iff_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:53:03.297577+00:00
-- url     : https://prove2.me/submissions/dbbff814-5e69-40cb-b9de-2a567897fe2c

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_generic_extended_infimum_lt_horizon
import Mathlib.Order.MinMax
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The minimum of the named strict passage clocks is before T exactly
when an actual strict two-sided crossing occurs before T.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (T : ℝ≥0) :
    (min (twoSidedExitUpTime X upper ω)
      (twoSidedExitDownTime X lower ω) < (T : ℝ≥0∞)) ↔
    ∃ s : ℝ≥0, s < T ∧
      (X.X s ω < lower ∨ upper < X.X s ω) := by
  have hU :
      (twoSidedExitUpTime X upper ω < (T : ℝ≥0∞)) ↔
      ∃ s : ℝ≥0, upper < X.X s ω ∧ s < T := by
    change (⨅ (s : ℝ≥0) (_ : upper < X.X s ω),
      (s : ℝ≥0∞)) < (T : ℝ≥0∞) ↔ _
    exact chat03_generic_extended_infimum_lt_horizon
      (fun s : ℝ≥0 => upper < X.X s ω) T
  have hD :
      (twoSidedExitDownTime X lower ω < (T : ℝ≥0∞)) ↔
      ∃ s : ℝ≥0, X.X s ω < lower ∧ s < T := by
    change (⨅ (s : ℝ≥0) (_ : X.X s ω < lower),
      (s : ℝ≥0∞)) < (T : ℝ≥0∞) ↔ _
    exact chat03_generic_extended_infimum_lt_horizon
      (fun s : ℝ≥0 => X.X s ω < lower) T
  constructor
  · intro h
    rcases min_lt_iff.mp h with hu | hd
    · obtain ⟨s, hs, hst⟩ := hU.mp hu
      exact ⟨s, hst, Or.inr hs⟩
    · obtain ⟨s, hs, hst⟩ := hD.mp hd
      exact ⟨s, hst, Or.inl hs⟩
  · rintro ⟨s, hst, h⟩
    rcases h with hd | hu
    · apply min_lt_iff.mpr (Or.inr ?_)
      exact hD.mpr ⟨s, hd, hst⟩
    · apply min_lt_iff.mpr (Or.inl ?_)
      exact hU.mpr ⟨s, hu, hst⟩
