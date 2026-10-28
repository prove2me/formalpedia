-- Prove2me | solution 1 for AvramDividend.Classical.chat04_reflected_infimum_Iic_iff_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:37:54.650043+00:00
-- url     : https://prove2.me/submissions/41ce534d-14b3-4c81-8bc4-379cdd564f32

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_lower_survival_running_infimum_equiv
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ω : Ω) (x : ℝ) :
    -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} ≤ x ↔
      ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω := by
  have hb := levy_path_bddBelow_finite_horizon X t ω
  rw [lower_survival_running_infimum_equiv X t ω hb x]
  constructor <;> intro h <;> linarith
