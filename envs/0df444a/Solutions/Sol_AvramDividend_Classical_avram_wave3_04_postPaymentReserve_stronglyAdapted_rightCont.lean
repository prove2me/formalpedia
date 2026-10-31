-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_postPaymentReserve_stronglyAdapted_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:56:11.568723+00:00
-- url     : https://prove2.me/submissions/44a2b485-4579-43f6-8941-c6a48d887798

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Under the genuine original Lévy law, the controlled post-payment
reserve is strongly adapted to the right-continuous filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    StronglyAdapted 𝓕.rightCont
      (fun t ω => x + X.X t ω - rightLimit D t ω) := by
  intro t
  exact ((postPaymentReserve_cadlag_adapted X x D hD).2.2 t).stronglyMeasurable
