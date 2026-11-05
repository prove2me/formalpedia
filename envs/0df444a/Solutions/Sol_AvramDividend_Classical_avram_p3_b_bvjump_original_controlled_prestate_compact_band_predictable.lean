-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:59:51.662912+00:00
-- url     : https://prove2.me/submissions/7488b61e-618d-4fe6-a3d8-91aeffd41fc7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine original prepayment left-limit compact-reserve event is
predictable and can therefore be used directly for marked P2 compensation. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (a b : ℝ) :
    MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω | Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2)
          p.1 ∈ Icc a b} := by
  have hPred := avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
    X x D hD
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hm : Measurable (fun p : ℝ≥0 × Ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) :=
    (show StronglyMeasurable (fun p : ℝ≥0 × Ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
      from hPred).measurable
  exact measurableSet_Icc.preimage hm
