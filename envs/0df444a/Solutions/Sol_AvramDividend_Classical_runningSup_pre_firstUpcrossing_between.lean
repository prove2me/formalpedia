-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_pre_firstUpcrossing_between
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T06:34:55.706994+00:00
-- url     : https://prove2.me/submissions/7ea80744-fb56-4fb9-a083-18f89f191e98

import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_prethreshold_le
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open AvramDividend.Classical
open Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞))) :
    ∀ t : ℝ≥0, t < u →
      0 ≤ runningSup X t ω ∧ runningSup X t ω ≤ b := by
  intro t ht
  obtain ⟨hsupEq, hnonneg⟩ := runningSup_eq_rawSup_nonneg X t ω
  constructor
  · exact hnonneg
  · rw [hsupEq]
    haveI : Nonempty (Set.Icc (0 : ℝ≥0) t) :=
      ⟨⟨0, by simp⟩⟩
    refine ciSup_le (fun (s : Set.Icc (0 : ℝ≥0) t) => ?_)
    have hslt : (s : ℝ≥0) < u :=
      lt_of_le_of_lt s.property.2 ht
    exact (firstUpcrossing_prethreshold_le X b ω u hu) s hslt
