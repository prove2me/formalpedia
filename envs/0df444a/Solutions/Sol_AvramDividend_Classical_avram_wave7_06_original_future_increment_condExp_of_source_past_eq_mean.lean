-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_future_increment_condExp_of_source_past_eq_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:45:32.545773+00:00
-- url     : https://prove2.me/submissions/a75de007-de6f-4b30-a996-2b9ba55e67b9

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_future_increment_L1_integrable_equal_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Actual original-filtration future increment conditional expectation equals its source mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hInt : Integrable (X.X t) P) :
    P[(fun ω => X.X (s + t) ω - X.X s ω) | 𝓕 s] =ᵐ[P]
      (fun _ => ∫ ω, X.X t ω ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let A : Ω → ℝ := fun ω => X.X (s + t) ω - X.X s ω
  have hEnd : Measurable (X.X (s + t)) := X.adapted.measurable
  have hStart : Measurable (X.X s) := X.adapted.measurable
  have hMeasA : Measurable A := by
    change Measurable (fun ω => X.X (s + t) ω - X.X s ω)
    exact hEnd.sub hStart
  have hleA : MeasurableSpace.comap A inferInstance ≤ mΩ :=
    (measurable_iff_comap_le).mp hMeasA
  have hlePast : 𝓕 s ≤ mΩ := 𝓕.le s
  have hMeasComap :
      Measurable[MeasurableSpace.comap A inferInstance] A :=
    (measurable_iff_comap_le).mpr le_rfl
  have hSM :
      StronglyMeasurable[MeasurableSpace.comap A inferInstance] A :=
    hMeasComap.stronglyMeasurable
  have hIndep :
      Indep (MeasurableSpace.comap A inferInstance) (𝓕 s) P := by
    simpa only [A] using X.indepIncrements s (s + t) (by simp)
  have hCE :
      P[A | 𝓕 s] =ᵐ[P] (fun _ => ∫ ω, A ω ∂P) :=
    condExp_indep_eq hleA hlePast hSM hIndep
  have hMean :=
    (avram_wave7_06_original_future_increment_L1_integrable_equal_mean
      X s t hInt).2
  change P[(fun ω => X.X (s + t) ω - X.X s ω) | 𝓕 s] =ᵐ[P]
    (fun _ => ∫ ω, X.X t ω ∂P)
  simpa only [A, hMean] using hCE
