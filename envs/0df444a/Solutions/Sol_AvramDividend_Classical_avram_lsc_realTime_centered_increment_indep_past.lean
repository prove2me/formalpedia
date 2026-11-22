-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_realTime_centered_increment_indep_past
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T15:30:47.688787+00:00
-- url     : https://prove2.me/submissions/a94b2186-990b-4b4d-924a-148ff48bdb32

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Real-time centred Gaussian increments remain independent of the source filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Indep
      (MeasurableSpace.comap (fun ω =>
        ((X.X (Real.toNNReal t) ω - X.X (Real.toNNReal s) ω) -
          (t - s) * X.c) / X.σ) inferInstance)
      (𝓕 (Real.toNNReal s)) P := by
  have hstNN : Real.toNNReal s ≤ Real.toNNReal t :=
    Real.toNNReal_le_toNNReal hst
  have hindep := X.indepIncrements (Real.toNNReal s) (Real.toNNReal t) hstNN
  let f : Ω → ℝ := fun ω =>
    X.X (Real.toNNReal t) ω - X.X (Real.toNNReal s) ω
  have hf : Measurable[MeasurableSpace.comap f inferInstance] f :=
    Measurable.of_comap_le le_rfl
  have hg : Measurable[MeasurableSpace.comap f inferInstance]
      (fun ω : Ω => (f ω - (t - s) * X.c) / X.σ) := by
    exact ((measurable_id.sub_const _).div_const _).comp hf
  have hsub := Measurable.comap_le hg
  exact indep_of_indep_of_le_left hindep hsub

