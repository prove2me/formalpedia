-- Prove2me | solution 1 for AvramDividend.Classical.tauceti_original_levy_stopped_rightCont_stronglyAdapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:03:39.013263+00:00
-- url     : https://prove2.me/submissions/b8ed83cb-a15d-45ea-8a06-7611d74e3fca

/- Copyright (c) 2026 The Tau Ceti contributors; Apache-2.0.
  Adapted from TauCeti's ContinuousStopping.lean stop and progressivity arguments.
  Depends on the accepted original right-grid TauCeti progressivity port. -/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_tauceti_original_levy_stronglyProgressive
open MeasureTheory Filter Set TopologicalSpace AvramDividend.Classical
open scoped NNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ) :
    StronglyAdapted 𝓕.rightCont (stoppedProcess X.X τ) := by
  have hprog : IsStronglyProgressive 𝓕.rightCont X.X := by
    intro T
    have hbase := tauceti_original_levy_stronglyProgressive X T
    apply hbase.mono
    change
      ((inferInstance : MeasurableSpace (Iic T)).prod (𝓕 T)) ≤
      ((inferInstance : MeasurableSpace (Iic T)).prod (𝓕.rightCont T))
    dsimp [MeasurableSpace.prod]
    exact sup_le_sup le_rfl (MeasurableSpace.comap_mono (𝓕.le_rightCont T))
  exact hprog.stronglyAdapted_stoppedProcess hτ

