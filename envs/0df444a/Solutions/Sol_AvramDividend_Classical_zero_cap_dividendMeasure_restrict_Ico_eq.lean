-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_dividendMeasure_restrict_Ico_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:31:00.862969+00:00
-- url     : https://prove2.me/submissions/fe7d86fb-4828-4acf-b46d-65df55c7018a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
import Theorems.Thm_AvramDividend_Classical_zero_cap_dividendMeasure_Ico_eq_barrier_before_ruin
import Theorems.Thm_AvramDividend_Classical_restricted_measure_eq_of_Ico_prefix_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
UNSUBMITTED dependency-stage source. Imported zero_cap_dividendMeasure_Ico...
and restricted_measure_eq... must both be remotely Proved first.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 0 D)
    (ω : Ω) (T : ℝ≥0) (hT : 0 < T)
    (hTr : (T : ℝ≥0∞) < ruinTime X 0 D ω) :
    (dividendMeasure D ω).restrict (Ico (0 : ℝ) (T : ℝ)) =
      (dividendMeasure (barrierStrategy X 0 0) ω).restrict
        (Ico (0 : ℝ) (T : ℝ)) := by
  apply restricted_measure_eq_of_Ico_prefix_eq
    (dividendMeasure D ω)
    (dividendMeasure (barrierStrategy X 0 0) ω) (T : ℝ)
  · rw [dividendMeasure_Ico_zero_eq_dividendValue D hD.1.1 ω T]
    exact ENNReal.ofReal_lt_top
  · intro a b ha0 hbT
    by_cases hba : b ≤ a
    · have hEmpty : Ico a b = ∅ := Ico_eq_empty_of_le hba
      simp [hEmpty]
    · have hab : a < b := lt_of_not_ge hba
      have hb0 : 0 < b := lt_of_le_of_lt ha0 hab
      let A : ℝ≥0 := ⟨a, ha0⟩
      let B : ℝ≥0 := ⟨b, le_of_lt hb0⟩
      have habNN : A ≤ B := hab.le
      have hBpos : 0 < B := hb0
      have hBT : B ≤ T := hbT
      have hBpre : (B : ℝ≥0∞) < ruinTime X 0 D ω :=
        lt_of_le_of_lt (by exact_mod_cast hBT) hTr
      have hAe : (A : ℝ) = a := rfl
      have hBe : (B : ℝ) = b := rfl
      rw [← hAe, ← hBe]
      exact zero_cap_dividendMeasure_Ico_eq_barrier_before_ruin
        X D hD ω A B habNN hBpos hBpre
