-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_successive_future_increments_indepFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:28:59.885121+00:00
-- url     : https://prove2.me/submissions/d80cedef-ef2d-4cc3-8dda-77f0469d7c0b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Consecutive original X increments are independent via adaptedness and the source filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s u v : ℝ≥0) :
    IndepFun
      (fun ω => X.X (s + u) ω - X.X s ω)
      (fun ω => X.X (s + u + v) ω - X.X (s + u) ω)
      P := by
  have hFirstMeas : Measurable[𝓕 (s + u)] (X.X (s + u)) :=
    X.adapted.measurable_le (le_refl (s + u))
  have hEarlierMeas : Measurable[𝓕 (s + u)] (X.X s) :=
    X.adapted.measurable_le (by simp : s ≤ s + u)
  have hPastMeas :
      Measurable[𝓕 (s + u)]
        (fun ω => X.X (s + u) ω - X.X s ω) := by
    letI : MeasurableSpace Ω := 𝓕 (s + u)
    exact hFirstMeas.sub hEarlierMeas
  have hPastLe :
      MeasurableSpace.comap
        (fun ω => X.X (s + u) ω - X.X s ω)
        inferInstance ≤ 𝓕 (s + u) :=
    (measurable_iff_comap_le).mp hPastMeas
  have hFuture :
      Indep
        (MeasurableSpace.comap
          (fun ω => X.X (s + u + v) ω - X.X (s + u) ω)
          inferInstance)
        (𝓕 (s + u)) P :=
    X.indepIncrements (s + u) (s + u + v) (by simp)
  have hPair :
      Indep
        (MeasurableSpace.comap
          (fun ω => X.X (s + u) ω - X.X s ω) inferInstance)
        (MeasurableSpace.comap
          (fun ω => X.X (s + u + v) ω - X.X (s + u) ω)
          inferInstance) P :=
    (indep_of_indep_of_le_right hFuture hPastLe).symm
  exact (IndepFun_iff_Indep _ _ P).2 hPair
