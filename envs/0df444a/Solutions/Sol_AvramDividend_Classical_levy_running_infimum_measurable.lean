-- Prove2me | solution 1 for AvramDividend.Classical.levy_running_infimum_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:33:29.059948+00:00
-- url     : https://prove2.me/submissions/a010767d-e2d2-416d-b75c-2ef9eae6a503

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Probability.Martingale.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Theorems.Thm_AvramDividend_Classical_lower_survival_running_infimum_equiv
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-- The negative running infimum is measurable in the Lévy sample path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) :
    Measurable (fun ω : Ω =>
      -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}) := by
  apply measurable_of_Iic
  intro a
  have heq :
      (fun ω : Ω => -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ t ∧ y = X.X s ω}) ⁻¹' Iic a =
      {ω : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ a + X.X s ω} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
    rw [lower_survival_running_infimum_equiv X t ω
      (levy_path_bddBelow_finite_horizon X t ω) a]
    constructor <;> intro h <;> linarith
  rw [heq]
  exact chat04_shifted_lower_survival_measurable_no_schedule X a t
