-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_actual_two_sided_horizon_killed_grid_three_way_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T12:18:17.770752+00:00
-- url     : https://prove2.me/submissions/9702e754-c0a8-483d-aa5d-c675e860df4a

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_up_first_iff_finite_stopped_min

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- Every source Lévy path lies in one of the three true killed-grid convergence regimes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a) (ω : Ω) (T : ℝ≥0) :
    (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω ∨
    (twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a-x) ω ∧
      (twoSidedExitDownTime X (-x) ω).toNNReal ≤ T) ∨
    (twoSidedExitUpTime X (a-x) ω < twoSidedExitDownTime X (-x) ω ∧
      (twoSidedExitUpTime X (a-x) ω).toNNReal < T) := by
  let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
  let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
  by_cases hBefore : (T : ℝ≥0∞) < D
  · exact Or.inl hBefore
  · have hDT : D ≤ (T : ℝ≥0∞) := le_of_not_gt hBefore
    have hDTfin : D < ⊤ :=
      lt_of_le_of_lt hDT (ENNReal.coe_lt_top : (T : ℝ≥0∞) < ⊤)
    rcases lt_trichotomy D U with hDown | hEq | hUp
    · have hCap : D.toNNReal ≤ T := by
        apply ENNReal.coe_le_coe.mp
        simpa only [ENNReal.coe_toNNReal (ne_of_lt hDTfin)] using hDT
      exact Or.inr (Or.inl ⟨hDown, hCap⟩)
    · have hUfin : U < ⊤ := by simpa only [hEq] using hDTfin
      have hContr : U < D :=
        (avram_root29_03_up_first_iff_finite_stopped_min
          X a x ha ω).2 ⟨min_eq_left hEq.ge, hUfin⟩
      exact False.elim ((not_lt_of_ge hEq.le) hContr)
    · have hUfin : U < ⊤ := lt_trans hUp hDTfin
      have hUT : U < (T : ℝ≥0∞) := lt_of_lt_of_le hUp hDT
      have hCap : U.toNNReal < T := by
        apply ENNReal.coe_lt_coe.mp
        simpa only [ENNReal.coe_toNNReal (ne_of_lt hUfin)] using hUT
      exact Or.inr (Or.inr ⟨hUp, hCap⟩)
