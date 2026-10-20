-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_right_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T12:48:05.028622+00:00
-- url     : https://prove2.me/submissions/1e6a5b46-7127-401d-894b-80869cf7e00d

import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_of_right_continuous
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun s => reflectedSup X s ω) (Set.Ici t) t := by
  obtain ⟨hMono, hDom⟩ := runningSup_monotone_and_path_le X ω
  have hRep : ∀ r : ℝ≥0,
      runningSup X r ω =
        (⨆ s : Set.Icc (0 : ℝ≥0) r, X.X s.1 ω) := by
    intro r
    exact (runningSup_eq_rawSup_nonneg X r ω).1
  have hRight : ∀ r : ℝ≥0,
      Tendsto (fun s : ℝ≥0 => X.X s ω)
        (𝓝[≥] r) (𝓝 (X.X r ω)) := by
    intro r
    exact (X.rightCont ω r).tendsto
  have hContS : ContinuousWithinAt
      (fun s : ℝ≥0 => runningSup X s ω) (Set.Ici t) t :=
    runningSup_right_continuous_of_right_continuous
      (fun s => X.X s ω) (fun s => runningSup X s ω)
      hMono hDom hRep hRight t
  change ContinuousWithinAt
    (fun s : ℝ≥0 => runningSup X s ω - X.X s ω) (Set.Ici t) t
  exact hContS.sub (X.rightCont ω t)
