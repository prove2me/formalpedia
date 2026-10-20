-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_dividendMeasure_restrict_paymentTimes_eq_of_pos_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T14:23:49.797788+00:00
-- url     : https://prove2.me/submissions/172375d5-4801-42cb-b72c-2281b0f8c376

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_iUnion_strict_rational_prefixes
import Theorems.Thm_AvramDividend_Classical_measure_restrict_iUnion_eq_of_countable_directed_prefix
import Theorems.Thm_AvramDividend_Classical_zero_cap_dividendMeasure_restrict_Ico_eq
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

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
    (ω : Ω) (hσ : 0 < ruinTime X 0 D ω) :
    (dividendMeasure D ω).restrict (paymentTimes (ruinTime X 0 D ω)) =
    (dividendMeasure (barrierStrategy X 0 0) ω).restrict
      (paymentTimes (ruinTime X 0 D ω)) := by
  let σ : ℝ≥0∞ := ruinTime X 0 D ω
  let I := {q : ℚ // 0 < (q : ℝ) ∧ ENNReal.ofReal (q : ℝ) < σ}
  let s : I → Set ℝ := fun q => Ico (0 : ℝ) (q : ℝ)
  have hd : Directed (· ⊆ ·) s := by
    intro i j
    rcases le_total (i : ℚ) (j : ℚ) with hij | hji
    · refine ⟨j, ?_, Subset.rfl⟩
      intro t ht
      exact ⟨ht.1, lt_of_lt_of_le ht.2 (by exact_mod_cast hij)⟩
    · refine ⟨i, Subset.rfl, ?_⟩
      intro t ht
      exact ⟨ht.1, lt_of_lt_of_le ht.2 (by exact_mod_cast hji)⟩
  have heq (q : I) :
      (dividendMeasure D ω).restrict (s q) =
      (dividendMeasure (barrierStrategy X 0 0) ω).restrict (s q) := by
    let T : ℝ≥0 := ⟨(q : ℝ), q.property.1.le⟩
    have hTpos : 0 < T := q.property.1
    have hTr : (T : ℝ≥0∞) < σ := by
      have hcoe : (T : ℝ≥0∞) = ENNReal.ofReal (q : ℝ) :=
        (ENNReal.ofReal_eq_coe_nnreal q.property.1.le).symm
      rw [hcoe]
      exact q.property.2
    have hTr' : (T : ℝ≥0∞) < ruinTime X 0 D ω := hTr
    have hTcast : (T : ℝ) = (q : ℝ) := rfl
    change (dividendMeasure D ω).restrict (Ico (0 : ℝ) (q : ℝ)) =
      (dividendMeasure (barrierStrategy X 0 0) ω).restrict
        (Ico (0 : ℝ) (q : ℝ))
    rw [← hTcast]
    exact zero_cap_dividendMeasure_restrict_Ico_eq X D hD ω T hTpos hTr'
  have hEqUnion :=
    measure_restrict_iUnion_eq_of_countable_directed_prefix
      (dividendMeasure D ω)
      (dividendMeasure (barrierStrategy X 0 0) ω) s hd heq
  change (dividendMeasure D ω).restrict (paymentTimes σ) =
    (dividendMeasure (barrierStrategy X 0 0) ω).restrict (paymentTimes σ)
  rw [paymentTimes_eq_iUnion_strict_rational_prefixes σ hσ]
  exact hEqUnion
