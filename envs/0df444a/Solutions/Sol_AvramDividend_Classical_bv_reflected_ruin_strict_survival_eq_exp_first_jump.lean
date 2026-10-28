-- Prove2me | solution 1 for AvramDividend.Classical.bv_reflected_ruin_strict_survival_eq_exp_first_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:40:29.554985+00:00
-- url     : https://prove2.me/submissions/1ce58a20-8605-42df-81c7-c81506f91f62

import Theorems.Thm_AvramDividend_Classical_bv_reflected_ruin_survival_ge_exp_first_jump
import Theorems.Thm_AvramDividend_Classical_bv_reflected_ruin_strict_survival_le_exp_first_jump
import Theorems.Thm_AvramDividend_Classical_exponential_right_squeeze
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The original finite-activity zero-reflected-barrier strict survival tail is exponential. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) :
    P.real {ω : Ω | (t : ℝ≥0∞) < barrierRuinTime X 0 ω} =
      Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let rate : ℝ := (X.ν (Iio (0 : ℝ))).toReal
  let A : Set Ω := {ω | (t : ℝ≥0∞) < barrierRuinTime X 0 ω}
  have hUpper : P.real A ≤ Real.exp (-((t : ℝ) * rate)) :=
    bv_reflected_ruin_strict_survival_le_exp_first_jump X hBV hFinite t
  have hLower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
      Real.exp (-(((t : ℝ) + epsilon) * rate)) ≤ P.real A := by
    let u : ℝ≥0 := t + Real.toNNReal epsilon
    have heps : ((Real.toNNReal epsilon : ℝ≥0) : ℝ) = epsilon :=
      Real.coe_toNNReal _ hepsilon.le
    have hu : (u : ℝ) = (t : ℝ) + epsilon := by
      simp only [u, NNReal.coe_add, heps]
    have htu : t < u := by
      dsimp [u]
      have hpos : 0 < Real.toNNReal epsilon := Real.toNNReal_pos.mpr hepsilon
      exact lt_add_of_pos_right t hpos
    have hsubset :
        {ω : Ω | (u : ℝ≥0∞) ≤ barrierRuinTime X 0 ω} ⊆ A := by
      intro ω hw
      exact lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr htu) hw
    calc
      Real.exp (-(((t : ℝ) + epsilon) * rate)) =
        Real.exp (-((u : ℝ) * rate)) := by rw [hu]
      _ ≤ P.real {ω : Ω | (u : ℝ≥0∞) ≤ barrierRuinTime X 0 ω} :=
        bv_reflected_ruin_survival_ge_exp_first_jump X
          hStanding hBV hFinite u
      _ ≤ P.real A := measureReal_mono hsubset
  exact exponential_right_squeeze (t : ℝ) rate (P.real A) hLower hUpper
