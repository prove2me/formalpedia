-- Prove2me | solution 1 for BanditAlgorithm.bretagnolle_huber_inequality_finite_typeStar
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T19:38:25.242928+00:00
-- url     : https://prove2.me/submissions/f0aba1f0-bd64-4a20-b99b-414f682b5023

import Theorems.Thm_BanditAlgorithm_bretagnolle_huber_inequality
import Theorems.Thm_InformationTheory_klDiv_map_measurableEmbedding
import Mathlib.Data.Fintype.EquivFin

open MeasureTheory InformationTheory Real
open scoped ENNReal

namespace BanditAlgorithm

theorem _root_.solution {Ω : Type*} [Fintype Ω] {mΩ : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set Ω} (hA : MeasurableSet A) (hD : klDiv P Q ≠ ∞) :
    2⁻¹ * exp (-(klDiv P Q).toReal) ≤ P.real A + Q.real Aᶜ := by
  let e : Ω ≃ Fin (Fintype.card Ω) := Fintype.equivFin Ω
  letI mS : MeasurableSpace (Fin (Fintype.card Ω)) := MeasurableSpace.map e mΩ
  have he : MeasurableEquiv Ω (Fin (Fintype.card Ω)) :=
    { toEquiv := e
      measurable_toFun := Measurable.of_le_map le_rfl
      measurable_invFun := by
        apply Measurable.of_le_map
        simp [mS, e] }
  let P' : Measure (Fin (Fintype.card Ω)) := P.map he
  let Q' : Measure (Fin (Fintype.card Ω)) := Q.map he
  haveI : IsProbabilityMeasure P' :=
    Measure.isProbabilityMeasure_map he.measurable.aemeasurable
  haveI : IsProbabilityMeasure Q' :=
    Measure.isProbabilityMeasure_map he.measurable.aemeasurable
  have hklP : klDiv P' Q' = klDiv P Q := by
    exact InformationTheory.klDiv_map_measurableEmbedding he.measurableEmbedding P Q
  have hA' : MeasurableSet (he '' A) := he.measurableSet_image.mpr hA
  have hbh := bretagnolle_huber_inequality P' Q' hA' (hklP ▸ hD)
  rw [hklP] at hbh
  have hPA : P'.real (he '' A) = P.real A := by
    simp only [Measure.real, P']
    rw [Measure.map_apply he.measurable hA']
    rw [he.preimage_image]
  have hQA : Q'.real (he '' A)ᶜ = Q.real Aᶜ := by
    simp only [Measure.real, Q']
    rw [Measure.map_apply he.measurable hA'.compl]
    rw [Set.preimage_compl, he.preimage_image]
  rwa [hPA, hQA] at hbh

end BanditAlgorithm
