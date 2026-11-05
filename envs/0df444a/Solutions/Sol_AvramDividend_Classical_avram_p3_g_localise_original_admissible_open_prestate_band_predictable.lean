-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_admissible_open_prestate_band_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:21:00.059054+00:00
-- url     : https://prove2.me/submissions/af9d4fb7-52c5-4752-8b6f-9b7489c5645d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every open band of the literal original admissible reserve prestate,
including rational C1 bands, is right-continuous predictable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (a b : ℝ) :
    MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω |
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈
          Ioo a b} := by
  have hP := avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
    X x D hD.1.1
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hm : Measurable (fun p : ℝ≥0 × Ω =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) :=
    (show StronglyMeasurable (fun p : ℝ≥0 × Ω =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
      from hP).measurable
  exact isOpen_Ioo.measurableSet.preimage hm
