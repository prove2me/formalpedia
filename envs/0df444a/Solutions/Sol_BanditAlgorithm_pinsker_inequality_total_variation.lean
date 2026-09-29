-- Prove2me | solution 1 for BanditAlgorithm.pinsker_inequality_total_variation
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-19T01:56:21.368503+00:00
-- url     : https://prove2.me/submissions/1515157b-b652-4ec6-87bf-deebc85309d3

import Theorems.Thm_BanditAlgorithm_pinsker_squared_event_difference

open MeasureTheory InformationTheory Real
open scoped ENNReal

theorem solution {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set Ω} (hA : MeasurableSet A) (hD : klDiv P Q ≠ ∞) :
    1 - Real.sqrt ((klDiv P Q).toReal / 2) ≤ P.real A + Q.real Aᶜ := by
  have hcore := BanditAlgorithm.pinsker_squared_event_difference P Q hA hD
  rw [probReal_compl_eq_one_sub hA]
  by_cases hQP : Q.real A ≤ P.real A
  · have hsqrt : 0 ≤ Real.sqrt ((klDiv P Q).toReal / 2) := Real.sqrt_nonneg _
    linarith
  · have hgap : 0 ≤ Q.real A - P.real A := sub_nonneg.mpr (le_of_not_ge hQP)
    have hDnonneg : 0 ≤ (klDiv P Q).toReal / 2 := by positivity
    have hsqrt_sq : (Real.sqrt ((klDiv P Q).toReal / 2)) ^ 2 =
        (klDiv P Q).toReal / 2 := Real.sq_sqrt hDnonneg
    have hgap_sq : (Q.real A - P.real A) ^ 2 ≤ (klDiv P Q).toReal / 2 := by
      linarith
    have hgap_le : Q.real A - P.real A ≤ Real.sqrt ((klDiv P Q).toReal / 2) := by
      nlinarith [Real.sqrt_nonneg ((klDiv P Q).toReal / 2)]
    linarith
