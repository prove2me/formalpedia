-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_original_stopped_upperstrip_occupation_le_full
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T08:18:54.196294+00:00
-- url     : https://prove2.me/submissions/9dc75f08-b03b-4915-9c26-a501c5325277

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB54cp_true_original_stopped_upperstrip_postpre_occupation_indicator_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The physical stopped occupation of the original dividend reserve in
an upper-cap strip is no larger than the full-horizon occupation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x b : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (ω : Ω)
    (hFullI : IntegrableOn
      (fun t : ℝ =>
        if b < riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0)
      (Ioo (0 : ℝ) (n : ℝ)) volume) :
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
          b < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) ≤
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if b < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) := by
  have hStopI :=
    (avram_gbB54cp_true_original_stopped_upperstrip_postpre_occupation_indicator_integrable
      X x b D hD n ρ hρstop ω).2
  apply integral_mono hStopI hFullI
  intro t
  by_cases hb : b < riskProcess X x D (Real.toNNReal t) ω
  · by_cases ht : t < (ρ ω : ℝ)
    · simp [hb, ht]
    · simp [hb, ht]
  · simp [hb]

