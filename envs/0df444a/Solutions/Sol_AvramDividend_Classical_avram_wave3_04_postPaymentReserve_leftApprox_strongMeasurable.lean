-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_postPaymentReserve_leftApprox_strongMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:10:23.080425+00:00
-- url     : https://prove2.me/submissions/cd68ed2b-f273-4374-95b4-3ec7ee368a79

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine controlled reserve's left-limit observable, represented
by a canonical bounded-past limit, is strongly measurable at time t. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (t : ℝ≥0) :
    StronglyMeasurable[𝓕.rightCont t]
      (fun ω => Filter.limUnder atTop
        (fun n : ℕ =>
          x + X.X (t - t / ((n : ℝ≥0) + 2)) ω -
            rightLimit D (t - t / ((n : ℝ≥0) + 2)) ω)) := by
  have hstrong (n : ℕ) : StronglyMeasurable[𝓕.rightCont t]
      (fun ω => x + X.X (t - t / ((n : ℝ≥0) + 2)) ω -
        rightLimit D (t - t / ((n : ℝ≥0) + 2)) ω) := by
    have hadapt := (postPaymentReserve_cadlag_adapted X x D hD).2.2
    have hmeas := hadapt (t - t / ((n : ℝ≥0) + 2))
    exact (hmeas.mono ((𝓕.rightCont).mono (tsub_le_self)) le_rfl).stronglyMeasurable
  letI : MeasurableSpace Ω := 𝓕.rightCont t
  exact StronglyMeasurable.limUnder hstrong
