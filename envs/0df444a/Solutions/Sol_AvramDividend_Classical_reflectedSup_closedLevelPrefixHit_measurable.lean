-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_closedLevelPrefixHit_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:30:51.712629+00:00
-- url     : https://prove2.me/submissions/fa276a4c-741a-4c2b-8b71-33a8f7917b63

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_reflectedSup_fullPrefixSup_adapted_of_dense
import Theorems.Thm_AvramDividend_Classical_usc_compact_prefix_hit_iff_ciSup_ge
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ≥0) (hS : S.Countable) (hDense : Dense S)
    (h0 : (0 : ℝ≥0) ∈ S)
    (t : ℝ≥0) (x : ℝ) :
    MeasurableSet[𝓕 t]
      {ω : Ω | ∃ s : ℝ≥0, s ≤ t ∧ x ≤ reflectedSup X s ω} := by
  have heq : {ω : Ω | ∃ s : ℝ≥0, s ≤ t ∧ x ≤ reflectedSup X s ω} =
      {ω | x ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, reflectedSup X s.1 ω} := by
    ext ω
    exact usc_compact_prefix_hit_iff_ciSup_ge (fun s => reflectedSup X s ω) t x
      (reflectedSup_upperSemicontinuousOn_Icc X ω t)
  rw [heq]
  exact measurableSet_le measurable_const
    (reflectedSup_fullPrefixSup_adapted_of_dense X S hS hDense h0 t)
