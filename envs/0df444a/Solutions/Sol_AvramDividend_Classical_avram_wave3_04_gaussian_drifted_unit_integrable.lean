-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_gaussian_drifted_unit_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T01:01:16.577868+00:00
-- url     : https://prove2.me/submissions/1748a282-3783-4796-b16e-ac85b3b786ea

import Mathlib
import Theorems.Thm_AvramDividend_Classical_canonical_brownian_realTime_bridge
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasIndepIncrements_readable
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_readable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

/-- The real Gaussian unit-time drifted increment is integrable. -/
theorem solution :
    Integrable (fun ω : ℝ≥0 → ℝ =>
      brownian 1 ω - brownian 0 ω - (1 : ℝ))
      gaussianLimit := by
  obtain ⟨W, hW⟩ := canonical_brownian_realTime_bridge
  have hpre : IsPreBrownianReal
      (fun (t : ℝ≥0) ω => W.W (t : ℝ) ω) gaussianLimit :=
    HasIndepIncrements.isPreBrownianReal_of_hasLaw
      (fun t => W.hasLaw_eval_readable t) W.hasIndepIncrements_readable
  have hi : Integrable
      (fun ω : ℝ≥0 → ℝ => W.W (1 : ℝ) ω) gaussianLimit :=
    hpre.integrable_eval 1
  have hd : Integrable
      (fun ω : ℝ≥0 → ℝ => W.W (1 : ℝ) ω - (1 : ℝ)) gaussianLimit :=
    hi.sub (integrable_const _)
  convert hd using 1
  funext ω
  rw [← hW (1 : ℝ≥0) ω]
  simp
