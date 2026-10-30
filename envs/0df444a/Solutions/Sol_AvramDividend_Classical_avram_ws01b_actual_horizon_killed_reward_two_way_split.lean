-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_actual_horizon_killed_reward_two_way_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T14:02:10.829995+00:00
-- url     : https://prove2.me/submissions/6ad954b0-92b9-4cc0-90d0-b92cfb83fc48

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_two_sided_strict_exit_no_finite_tie

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- At every horizon the actual killed stopped reward splits into completed upper exit and surviving strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (a x : ℝ) (ha : 0 < a) (hxa : x ≤ a)
    (T : ℝ≥0) (ω : Ω) :
    (let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
     let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
     (if (T : ℝ≥0∞) < D then
        if min U D < ⊤ then
          Real.exp (-(q * ((min (min U D).toNNReal T) : ℝ))) *
            W (x + X.X (min (min U D).toNNReal T) ω)
        else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
      else if D < U then 0
      else Real.exp (-(q * (U.toNNReal : ℝ))) *
        W (x + X.X U.toNNReal ω)) =
     (if U < D ∧ U.toNNReal ≤ T then
        Real.exp (-(q * (U.toNNReal : ℝ))) *
          W (x + X.X U.toNNReal ω) else 0) +
     (if (T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D then
        Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω) else 0)) := by
  let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
  let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
  change (if (T : ℝ≥0∞) < D then
      if min U D < ⊤ then
        Real.exp (-(q * ((min (min U D).toNNReal T) : ℝ))) *
          W (x + X.X (min (min U D).toNNReal T) ω)
      else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
    else if D < U then 0 else
      Real.exp (-(q * (U.toNNReal : ℝ))) *
        W (x + X.X U.toNNReal ω)) =
    (if U < D ∧ U.toNNReal ≤ T then
      Real.exp (-(q * (U.toNNReal : ℝ))) *
        W (x + X.X U.toNNReal ω) else 0) +
    (if (T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D then
      Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω) else 0)
  rcases lt_trichotomy U D with hUp | hEq | hDown
  · have hUfin : U < ⊤ := lt_of_lt_of_le hUp le_top
    have hCoe : (U.toNNReal : ℝ≥0∞) = U :=
      ENNReal.coe_toNNReal (ne_of_lt hUfin)
    have hFin : min U D < ⊤ := by
      simpa only [min_eq_left hUp.le] using hUfin
    by_cases hUT : U.toNNReal ≤ T
    · have hUT' : U ≤ (T : ℝ≥0∞) := by
        rw [← hCoe]
        exact ENNReal.coe_le_coe.mpr hUT
      have hNotTU : ¬ (T : ℝ≥0∞) < U := not_lt.mpr hUT'
      by_cases hTD : (T : ℝ≥0∞) < D
      · have hUpper : U < D ∧ U.toNNReal ≤ T := ⟨hUp, hUT⟩
        have hSurvNot : ¬ ((T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D) := by
          intro hBoth
          exact hNotTU hBoth.1
        have hUTReal : (U.toNNReal : ℝ) ≤ (T : ℝ) := by
          exact_mod_cast hUT
        simp only [if_pos hTD, min_eq_left hUp.le, if_pos hUfin,
          min_eq_left hUT, min_eq_left hUTReal,
          if_pos hUpper, if_neg hSurvNot, add_zero]
      · have hNotDown : ¬ D < U := not_lt_of_ge hUp.le
        have hUpper : U < D ∧ U.toNNReal ≤ T := ⟨hUp, hUT⟩
        have hSurvNot : ¬ ((T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D) := by
          intro hBoth
          exact hNotTU hBoth.1
        simp only [if_neg hTD, if_neg hNotDown, if_pos hUpper,
          if_neg hSurvNot, add_zero]
    · have hTlt : T < U.toNNReal := lt_of_not_ge hUT
      have hTU : (T : ℝ≥0∞) < U := by
        rw [← hCoe]
        exact ENNReal.coe_lt_coe.mpr hTlt
      have hTD : (T : ℝ≥0∞) < D := lt_trans hTU hUp
      have hUpperNot : ¬ (U < D ∧ U.toNNReal ≤ T) := by
        intro hUpper
        exact hUT hUpper.2
      have hSurv : (T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D :=
        ⟨hTU, hTD⟩
      have hTltReal : (T : ℝ) < (U.toNNReal : ℝ) := by
        exact_mod_cast hTlt
      simp only [if_pos hTD, min_eq_left hUp.le, if_pos hUfin,
        min_eq_right (le_of_lt hTlt), min_eq_right hTltReal.le,
        if_neg hUpperNot, if_pos hSurv, zero_add]
  · have hUinf : U = ⊤ :=
      chat04_two_sided_strict_exit_no_finite_tie X a x ha hxa ω hEq
    have hDinf : D = ⊤ := hEq.symm.trans hUinf
    simp [hUinf, hDinf]
  · have hDfin : D < ⊤ := lt_of_lt_of_le hDown le_top
    have hCoe : (D.toNNReal : ℝ≥0∞) = D :=
      ENNReal.coe_toNNReal (ne_of_lt hDfin)
    have hFin : min U D < ⊤ := by
      simpa only [min_eq_right hDown.le] using hDfin
    by_cases hTD : (T : ℝ≥0∞) < D
    · have hTU : (T : ℝ≥0∞) < U := lt_trans hTD hDown
      have hTlt : T < D.toNNReal := by
        rw [← hCoe] at hTD
        exact ENNReal.coe_lt_coe.mp hTD
      have hNotUpper : ¬ (U < D ∧ U.toNNReal ≤ T) := by
        intro hUpper
        exact (not_lt_of_ge hDown.le) hUpper.1
      have hSurv : (T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D :=
        ⟨hTU, hTD⟩
      have hTltReal : (T : ℝ) < (D.toNNReal : ℝ) := by
        exact_mod_cast hTlt
      simp only [if_pos hTD, min_eq_right hDown.le, if_pos hDfin,
        min_eq_right (le_of_lt hTlt), min_eq_right hTltReal.le,
        if_neg hNotUpper, if_pos hSurv, zero_add]
    · have hNotUp : ¬ U < D := not_lt_of_ge hDown.le
      simp [hTD, hDown, hNotUp]
