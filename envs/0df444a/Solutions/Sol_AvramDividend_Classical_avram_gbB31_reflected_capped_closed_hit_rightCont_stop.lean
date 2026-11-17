-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB31_reflected_capped_closed_hit_rightCont_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:01:19.312624+00:00
-- url     : https://prove2.me/submissions/31a0b5c6-d9ef-4fc3-a15b-bafae23a748f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_firstClosedHit_isStoppingTime
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ≥0) (hS : S.Countable) (hDense : Dense S)
    (h0 : (0 : ℝ≥0) ∈ S)
    (H : ℝ≥0) (x : ℝ) :
    IsStoppingTime 𝓕.rightCont (fun ω : Ω =>
      WithTop.some (sInf ((Icc (0 : ℝ≥0) H ∩
        (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}))) := by 
  have hStop :=
    reflectedSup_capped_firstClosedHit_isStoppingTime
      X S hS hDense h0 H x
  intro t
  exact ((MeasurableSpace.le_def).mp
    ((Filtration.le_rightCont 𝓕) t)) _ (hStop t)
