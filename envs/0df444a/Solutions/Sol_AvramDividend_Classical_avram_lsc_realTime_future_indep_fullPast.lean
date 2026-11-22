-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_realTime_future_indep_fullPast
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T15:57:19.969094+00:00
-- url     : https://prove2.me/submissions/a6a2ec9b-29dc-4b98-afa0-ceddff2920a7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_lsc_realTime_centered_increment_indep_past

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

/-- The full past path of the original source is independent of its future centred real-time increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Indep
      (MeasurableSpace.comap
        (fun ω : Ω => fun u : Set.Iic (Real.toNNReal s) => X.X u ω)
        inferInstance)
      (MeasurableSpace.comap (fun ω =>
        ((X.X (Real.toNNReal t) ω - X.X (Real.toNNReal s) ω) -
          (t - s) * X.c) / X.σ) inferInstance) P := by
  have hpast : Measurable[𝓕 (Real.toNNReal s)]
      (fun ω : Ω => fun u : Set.Iic (Real.toNNReal s) => X.X u ω) := by
    have hi (u : Set.Iic (Real.toNNReal s)) :
        Measurable[𝓕 (Real.toNNReal s)] (X.X u) :=
      (X.adapted u).mono (𝓕.mono u.property) le_rfl
    letI : MeasurableSpace Ω := 𝓕 (Real.toNNReal s)
    exact measurable_pi_lambda _ hi
  have hfuture :=
    AvramDividend.Classical.avram_lsc_realTime_centered_increment_indep_past
      X s t hs hst
  exact indep_of_indep_of_le_left hfuture.symm (Measurable.comap_le hpast)

