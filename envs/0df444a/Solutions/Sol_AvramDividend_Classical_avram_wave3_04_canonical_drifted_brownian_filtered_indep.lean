-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_canonical_drifted_brownian_filtered_indep
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:59:19.101902+00:00
-- url     : https://prove2.me/submissions/1be6fae0-1701-410b-b34d-00d6c4f94ba5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_canonical_brownian_realTime_bridge
import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_natural_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_drifted_preBrownian_filtered_indep
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasIndepIncrements_readable
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_readable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

/-- Actual canonical drifted Brownian increments are independent of the natural past. -/
theorem solution :
    let B : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
      fun t ω => brownian t ω - brownian 0 ω - (t : ℝ)
    ∃ hmeas : ∀ t : ℝ≥0, StronglyMeasurable (B t),
      ∀ s t : ℝ≥0, s ≤ t →
        Indep (MeasurableSpace.comap
          (fun ω => B t ω - B s ω) inferInstance)
          ((Filtration.natural B hmeas) s) gaussianLimit := by
  intro B
  obtain ⟨hmeas, _⟩ := canonical_drifted_brownian_natural_adapted
  obtain ⟨W, hW⟩ := canonical_brownian_realTime_bridge
  let U : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
    fun t ω => W.W (t : ℝ) ω
  have hU : U = (fun t ω => brownian t ω - brownian 0 ω) := by
    funext t ω
    exact hW t ω
  have hpre : IsPreBrownianReal U gaussianLimit :=
    HasIndepIncrements.isPreBrownianReal_of_hasLaw
      (fun t => W.hasLaw_eval_readable t) W.hasIndepIncrements_readable
  have hmeasU : ∀ t : ℝ≥0,
      StronglyMeasurable (fun ω => U t ω - (t : ℝ)) := by
    intro t
    rw [hU]
    exact hmeas t
  refine ⟨hmeas, fun s t hst => ?_⟩
  have h := avram_wave3_04_drifted_preBrownian_filtered_indep
    U hpre hmeasU s t hst
  simpa only [hU] using h
