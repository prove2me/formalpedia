-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_dividendMeasure_Ico_eq_barrier_before_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T12:52:27.347406+00:00
-- url     : https://prove2.me/submissions/9e5f55a5-1c51-4bf9-a303-5b49732a8b93

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_eq_dividend_increment
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_zero_cap_barrier_eq_control_before_ruin
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 0 D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b) (hb : 0 < b)
    (hbr : (b : ℝ≥0∞) < ruinTime X 0 D ω) :
    dividendMeasure D ω (Ico (a : ℝ) (b : ℝ)) =
      dividendMeasure (barrierStrategy X 0 0) ω
        (Ico (a : ℝ) (b : ℝ)) := by
  have hd : IsDividendStrategy 𝓕 D := hD.1.1
  have hB : IsDividendStrategy 𝓕 (barrierStrategy X 0 0) :=
    barrierStrategy_isDividendStrategy_nonnegative_barrier X 0 0 (le_refl 0) (le_refl 0)
  have hbt : barrierStrategy X 0 0 b ω = D b ω :=
    zero_cap_barrier_eq_control_before_ruin X D hD ω b hb hbr
  have hat : barrierStrategy X 0 0 a ω = D a ω := by
    by_cases ha : a = 0
    · simp [ha, barrierStrategy, hD.1.1.1 ω]
    · have ha0 : 0 < a :=
        lt_of_le_of_ne (show (0 : ℝ≥0) ≤ a from zero_le) (Ne.symm ha)
      have har : (a : ℝ≥0∞) < ruinTime X 0 D ω :=
        lt_of_le_of_lt (by exact_mod_cast hab) hbr
      exact zero_cap_barrier_eq_control_before_ruin X D hD ω a ha0 har
  calc
    dividendMeasure D ω (Ico (a : ℝ) (b : ℝ)) =
        ENNReal.ofReal (D b ω - D a ω) :=
      dividendMeasure_Ico_eq_dividend_increment D hd ω a b
    _ = ENNReal.ofReal
        (barrierStrategy X 0 0 b ω - barrierStrategy X 0 0 a ω) := by
      rw [hbt, hat]
    _ = dividendMeasure (barrierStrategy X 0 0) ω
        (Ico (a : ℝ) (b : ℝ)) :=
      (dividendMeasure_Ico_eq_dividend_increment
        (barrierStrategy X 0 0) hB ω a b).symm
