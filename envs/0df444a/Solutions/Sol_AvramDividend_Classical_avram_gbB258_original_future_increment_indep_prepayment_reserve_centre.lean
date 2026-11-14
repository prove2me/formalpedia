-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB258_original_future_increment_indep_prepayment_reserve_centre
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T16:19:29.799348+00:00
-- url     : https://prove2.me/submissions/28520e06-6141-4677-a5a2-fed6f2e18b1a

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Future original Levy increments are independent of the prepayment reserve centre. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s t : ℝ≥0) (hst : s ≤ t) (x b : ℝ) :
    Indep
      (MeasurableSpace.comap (fun ω => X.X t ω - X.X s ω) inferInstance)
      (MeasurableSpace.comap (fun ω => b - x - X.X s ω + D s ω) inferInstance) P := by
  have hX : Measurable[𝓕 s] (X.X s) := X.adapted s
  have hDmeas : Measurable[𝓕 s] (D s) := hD.2.2.2 s
  have hCentre : Measurable[𝓕 s] (fun ω => b - x - X.X s ω + D s ω) := by
    fun_prop
  have hLE :
      MeasurableSpace.comap (fun ω => b - x - X.X s ω + D s ω)
        inferInstance ≤ 𝓕 s := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hA
    exact hCentre hB
  exact indep_of_indep_of_le_right (X.indepIncrements s t hst) hLE
