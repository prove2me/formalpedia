-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_centred_increment_indep_past
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:16:05.814992+00:00
-- url     : https://prove2.me/submissions/f6a7c77a-d3d6-4ff9-b046-24e3b07c30a6

import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

/-- The centred increment of the original Levy process is independent of its past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) :
    Indep
      (MeasurableSpace.comap
        (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)
        inferInstance)
      (𝓕 s) P := by
  let f : ℝ → ℝ := fun z => z - ((t - s : ℝ≥0) : ℝ) * Y.c
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  apply (Indep_iff _ _ P).2
  intro A B hA hB
  obtain ⟨C, hC, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hA
  have hPre : MeasurableSet (f ⁻¹' C) := hf hC
  have hPreΩ :
      MeasurableSet[MeasurableSpace.comap
        (fun ω => Y.X t ω - Y.X s ω) inferInstance]
        ((fun ω => Y.X t ω - Y.X s ω) ⁻¹' (f ⁻¹' C)) :=
    (MeasurableSpace.measurableSet_comap).2 ⟨f ⁻¹' C, hPre, rfl⟩
  have hBase := (Indep_iff _ _ P).1 (Y.indepIncrements s t hst)
    ((fun ω => Y.X t ω - Y.X s ω) ⁻¹' (f ⁻¹' C)) B hPreΩ hB
  simpa only [Set.preimage_preimage, Function.comp_def, f] using hBase
