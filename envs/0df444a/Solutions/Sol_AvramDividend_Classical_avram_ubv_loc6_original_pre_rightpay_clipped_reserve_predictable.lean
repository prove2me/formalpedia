-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_original_pre_rightpay_clipped_reserve_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:55:20.313394+00:00
-- url     : https://prove2.me/submissions/ab9c7a13-ff09-40b9-a565-ed553a17936b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original physical pre-right-dividend reserve remains predictable after
    clipping to any real compact band; this uses the right-continuous filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (δ v : ℝ) :
    Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
        if y ∈ Icc δ v then y else δ) := by
  classical
  have hp : IsStronglyPredictable 𝓕.rightCont
      (fun t ω => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD.1.1
  change StronglyMeasurable[𝓕.rightCont.predictable]
    (fun p : ℝ≥0 × Ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) at hp
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hY : Measurable (fun p : ℝ≥0 × Ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) :=
    hp.measurable
  have hband : MeasurableSet {p : ℝ≥0 × Ω |
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc δ v} :=
    measurableSet_Icc.preimage hY
  exact hY.ite hband measurable_const
