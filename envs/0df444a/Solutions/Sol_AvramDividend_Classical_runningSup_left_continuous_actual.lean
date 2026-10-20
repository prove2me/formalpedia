-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_left_continuous_actual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:31:38.890005+00:00
-- url     : https://prove2.me/submissions/4f257db9-cee6-415f-abda-9e817deec8d7

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_left_continuous_of_no_upward_jump
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ContinuousWithinAt (fun s : ℝ≥0 => runningSup X s ω) (Set.Iio t) t := by
  obtain ⟨hM, hDom⟩ := runningSup_monotone_and_path_le X ω
  have hRep (r : ℝ≥0) :
      runningSup X r ω =
        (⨆ s : Set.Icc (0 : ℝ≥0) r, X.X s.1 ω) :=
    (runningSup_eq_rawSup_nonneg X r ω).1
  obtain ⟨ℓ, hLeft⟩ := X.leftLim ω t ht
  exact runningSup_left_continuous_of_no_upward_jump
    (fun r : ℝ≥0 => X.X r ω)
    (fun r : ℝ≥0 => runningSup X r ω)
    hM hDom hRep t ht ℓ hLeft (X.noPosJumps ω t ℓ ht hLeft)
