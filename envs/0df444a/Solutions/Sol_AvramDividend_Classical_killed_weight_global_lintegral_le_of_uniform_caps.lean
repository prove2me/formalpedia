-- Prove2me | solution 1 for AvramDividend.Classical.killed_weight_global_lintegral_le_of_uniform_caps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T00:28:19.241825+00:00
-- url     : https://prove2.me/submissions/a6326517-4b44-4eac-b47d-e51b9ae89046

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_ennreal_killed_weight_eq_iSup_finite_clock_cap
import Theorems.Thm_AvramDividend_Classical_killed_weight_nat_caps_monotone
import Theorems.Thm_AvramDividend_Classical_killed_weight_nat_caps_measurable
import Theorems.Thm_AvramDividend_Classical_monotone_localised_reward_lintegral_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (T : Ω → ℝ≥0∞) (hT : Measurable T)
    (weight : Ω → ℝ≥0∞) (hw : Measurable weight)
    (hzero : ∀ ω, T ω = ⊤ → weight ω = 0)
    (bound : ℝ≥0∞)
    (hbound : ∀ n : ℕ,
      (∫⁻ ω, if T ω ≤ (n : ℝ≥0∞) then weight ω else 0 ∂P) ≤ bound) :
    (∫⁻ ω, weight ω ∂P) ≤ bound := by
  have hcap := monotone_localised_reward_lintegral_le P
    (fun n : ℕ => fun ω : Ω =>
      if T ω ≤ (n : ℝ≥0∞) then weight ω else 0)
    (killed_weight_nat_caps_measurable T hT weight hw)
    (killed_weight_nat_caps_monotone T weight)
    bound hbound
  have hfun :
      (fun ω : Ω =>
        ⨆ n : ℕ, if T ω ≤ (n : ℝ≥0∞) then weight ω else 0) =
      weight := by
    funext ω
    exact ennreal_killed_weight_eq_iSup_finite_clock_cap T weight hzero ω
  simpa only [hfun] using hcap
