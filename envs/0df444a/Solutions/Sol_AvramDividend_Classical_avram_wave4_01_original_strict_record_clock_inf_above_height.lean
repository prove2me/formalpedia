-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_strict_record_clock_inf_above_height
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:41:29.077147+00:00
-- url     : https://prove2.me/submissions/9842422a-ebbb-4f88-9ce2-3e3e709876d5

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- Strict level passage is the infimum of passage times at higher levels. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (h : ℝ) (ω : Ω) :
    twoSidedExitUpTime X h ω =
      ⨅ r : {r : ℝ // h < r}, twoSidedExitUpTime X r.1 ω := by
  apply le_antisymm
  · apply le_iInf
    intro r
    exact twoSidedExitUpTime_mono_threshold X h r.1 (le_of_lt r.2) ω
  · change (⨅ r : {r : ℝ // h < r}, twoSidedExitUpTime X r.1 ω) ≤
        (⨅ t : ℝ≥0, ⨅ ht : h < X.X t ω, (t : ℝ≥0∞))
    refine le_iInf fun t => le_iInf fun ht => ?_
    let r : ℝ := (h + X.X t ω) / 2
    have hr1 : h < r := by
      dsimp [r]
      linarith
    have hr2 : r < X.X t ω := by
      dsimp [r]
      linarith
    have hhit : twoSidedExitUpTime X r ω ≤ (t : ℝ≥0∞) := by
      unfold twoSidedExitUpTime
      exact iInf_le_of_le t (iInf_le_of_le hr2 le_rfl)
    calc
      (⨅ s : {s : ℝ // h < s}, twoSidedExitUpTime X s.1 ω) ≤
          twoSidedExitUpTime X r ω :=
            iInf_le _ (⟨r, hr1⟩ : {s : ℝ // h < s})
      _ ≤ (t : ℝ≥0∞) := hhit
