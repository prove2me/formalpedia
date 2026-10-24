-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_old_paymentTimes_identity_false_if_preRuin_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T17:02:30.760029+00:00
-- url     : https://prove2.me/submissions/54d3ba8c-a428-4393-9544-86bd140da2cc

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_paymentTimes_after_firstUpcrossing_no_preRuin_breach
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A genuine post-crossing survival time refutes the old strict-breach set identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (ω : Ω) (u : ℝ≥0)
    (hdraw : ∀ s : ℝ≥0,
      riskProcess X x (barrierStrategy X x a) (u + s) ω < 0 ↔
        a < runningSup X (u + s) ω - X.X (u + s) ω)
    (hwitness : ∃ t : ℝ≥0, u < t ∧
      (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω) :
    {t : ℝ≥0 | u < t ∧
        (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω} ≠
      {t : ℝ≥0 | u < t ∧
        (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω ∧
        a < runningSup X t ω - X.X t ω} := by
  intro hset
  obtain ⟨t, htpost, htpre⟩ := hwitness
  have hmem :
      t ∈ {s : ℝ≥0 | u < s ∧
        (s : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω} :=
    ⟨htpost, htpre⟩
  have hcorrect := hmem
  rw [barrierStrategy_paymentTimes_after_firstUpcrossing_no_preRuin_breach
      X x a ω u hdraw] at hcorrect
  rw [hset] at hmem
  exact hcorrect.2.2 hmem.2.2
