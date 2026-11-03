-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_inclusive_ruin_predictable_strict_hjb_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:42:21.749816+00:00
-- url     : https://prove2.me/submissions/bb2cbed1-1c27-41b0-b76d-dae89302e787

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The actual inclusive ruin-stop interior is predictable. The inclusion of
the ruin instant is essential for totally inaccessible source ruin jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) :
    MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
        0 < Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
        ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1) < C} := by
  let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
    Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t
  let τ : Ω → ℝ≥0∞ := ruinTime X x D
  have hYpred : IsStronglyPredictable 𝓕.rightCont Y :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD
  have hYm : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => Y p.1 p.2) :=
    hYpred.measurable
  have hτ : IsStoppingTime 𝓕.rightCont τ :=
    ruinTime_stopping_rightCont_filtration X x D hD
  have hS : IsStronglyPredictable 𝓕.rightCont
      (fun t ω => if (t : ℝ≥0∞) ≤ τ ω then (1 : ℝ) else 0) :=
    avram_wave3_04_inclusiveSurvival_stronglyPredictable τ hτ
  have hSm : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω =>
        if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0) :=
    hS.measurable
  have hSurv : MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω | (p.1 : ℝ≥0∞) ≤ τ p.2} := by
    have hpre : MeasurableSet[𝓕.rightCont.predictable]
        ((fun p : ℝ≥0 × Ω =>
          if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0) ⁻¹' {1}) :=
      hSm (measurableSet_singleton (1 : ℝ))
    convert hpre using 1
    ext p
    simp
  have hPos : MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω | 0 < Y p.1 p.2} :=
    measurableSet_lt measurable_const hYm
  have hCap : MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω | ENNReal.ofReal (Y p.1 p.2) < C} :=
    measurableSet_lt hYm.ennreal_ofReal measurable_const
  simpa only [Y, τ, Set.setOf_and] using hSurv.inter (hPos.inter hCap)
