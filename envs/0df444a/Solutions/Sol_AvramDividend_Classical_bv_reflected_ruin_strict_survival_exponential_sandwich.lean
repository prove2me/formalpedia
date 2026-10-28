-- Prove2me | solution 1 for AvramDividend.Classical.bv_reflected_ruin_strict_survival_exponential_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:46:10.32393+00:00
-- url     : https://prove2.me/submissions/99b8f289-277e-4ed3-aba9-4eadbb21667f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_bv_reflected_ruin_strict_survival_le_exp_first_jump
import Theorems.Thm_AvramDividend_Classical_bv_reflected_ruin_survival_ge_exp_first_jump
import Mathlib.MeasureTheory.Measure.Real
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The actual strict zero-barrier survival tail has matching exponential
upper and arbitrarily close time-shifted lower bounds. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t ε : ℝ≥0) (hε : 0 < ε) :
    Real.exp (-((((t + ε : ℝ≥0) : ℝ) *
      (X.ν (Iio (0 : ℝ))).toReal))) ≤
        P.real {ω : Ω | (t : ℝ≥0∞) < barrierRuinTime X 0 ω} ∧
    P.real {ω : Ω | (t : ℝ≥0∞) < barrierRuinTime X 0 ω} ≤
      Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have htlt : (t : ℝ≥0∞) < ((t + ε : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast (lt_add_of_pos_right t hε)
  have hSub :
      {ω : Ω | ((t + ε : ℝ≥0) : ℝ≥0∞) ≤ barrierRuinTime X 0 ω} ⊆
      {ω : Ω | (t : ℝ≥0∞) < barrierRuinTime X 0 ω} := by
    intro ω hω
    exact lt_of_lt_of_le htlt hω
  constructor
  · calc
      Real.exp (-((((t + ε : ℝ≥0) : ℝ) *
        (X.ν (Iio (0 : ℝ))).toReal))) ≤
          P.real {ω : Ω |
            ((t + ε : ℝ≥0) : ℝ≥0∞) ≤ barrierRuinTime X 0 ω} :=
        bv_reflected_ruin_survival_ge_exp_first_jump
          X hStanding hBV hFinite (t + ε)
      _ ≤ P.real {ω : Ω | (t : ℝ≥0∞) < barrierRuinTime X 0 ω} :=
        measureReal_mono hSub
  · exact bv_reflected_ruin_strict_survival_le_exp_first_jump
      X hBV hFinite t
