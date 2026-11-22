-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_realTime_future_indep_finitePast
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T15:57:09.890579+00:00
-- url     : https://prove2.me/submissions/f5066eaf-9f3c-4a0b-8a62-bfd25c603133

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_lsc_realTime_centered_increment_indep_past

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite-dimensional past and the original real-time source increment are independent. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {m : ℕ} (v : Fin m → ℝ≥0)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (hv : ∀ i, v i ≤ Real.toNNReal s) :
    Indep
      (MeasurableSpace.comap
        (fun ω : Ω => fun i : Fin m => X.X (v i) ω) inferInstance)
      (MeasurableSpace.comap (fun ω =>
        ((X.X (Real.toNNReal t) ω - X.X (Real.toNNReal s) ω) -
          (t - s) * X.c) / X.σ) inferInstance) P := by
  have hpast : Measurable[𝓕 (Real.toNNReal s)]
      (fun ω : Ω => fun i : Fin m => X.X (v i) ω) := by
    have hi (i : Fin m) : Measurable[𝓕 (Real.toNNReal s)] (X.X (v i)) :=
      (X.adapted (v i)).mono (𝓕.mono (hv i)) le_rfl
    letI : MeasurableSpace Ω := 𝓕 (Real.toNNReal s)
    exact measurable_pi_lambda _ hi
  have hfuture :=
    AvramDividend.Classical.avram_lsc_realTime_centered_increment_indep_past
      X s t hs hst
  exact indep_of_indep_of_le_left hfuture.symm (Measurable.comap_le hpast)

