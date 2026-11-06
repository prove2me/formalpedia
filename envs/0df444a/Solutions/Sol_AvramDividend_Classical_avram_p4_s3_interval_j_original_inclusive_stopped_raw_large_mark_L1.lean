-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_j_original_inclusive_stopped_raw_large_mark_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:26:07.297932+00:00
-- url     : https://prove2.me/submissions/dec67693-9522-4447-9b37-64b34dfb2673

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_j_original_inclusive_stopped_prejump_cap_large_mark_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original physical stopped raw large-jump generator is L1 on an explicitly
capped interior reserve region, with zero contribution after the true stop. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hStoppedReserveCap : ∀ p : ℝ≥0 × Ω,
      (p.1 : ℝ≥0∞) ≤ τ p.2 →
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc 0 v)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    [IsFiniteMeasure μ] :
    (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
     let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1;
    Integrable
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then
          w (Y p.1 + p.2) - w (Y p.1)
        else 0)
      (μ.prod (X.ν.restrict (Iio (-ε))))) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) :=
    𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod inferInstance
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s p.2 - rightLimit D s p.2) p.1
  let R : ℝ≥0 × Ω → ℝ := fun p =>
    (if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0) * Y p
  have hRaw : Integrable
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        w (R p.1 + p.2) - w (R p.1))
      (μ.prod (X.ν.restrict (Iio (-ε)))) := by
    simpa only [R, Y] using
      (avram_p4_s3_interval_j_original_inclusive_stopped_prejump_cap_large_mark_L1
        X x D hD τ hτ v ε hv hε hStoppedReserveCap
        w hw_cont hw_neg μ)
  have hStop : Measurable (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0) :=
    (avram_wave3_04_inclusiveSurvival_stronglyPredictable
      τ hτ).measurable
  have hSP : Measurable (fun p : (ℝ≥0 × Ω) × ℝ =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then (1 : ℝ) else 0) :=
    hStop.comp measurable_fst
  let E : Set ((ℝ≥0 × Ω) × ℝ) := {p |
    (if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then (1 : ℝ) else 0) = 1}
  have hE : MeasurableSet E :=
    hSP (measurableSet_singleton (1 : ℝ))
  have hInt := hRaw.indicator hE
  have hEq : E.indicator (fun p : (ℝ≥0 × Ω) × ℝ =>
      w (R p.1 + p.2) - w (R p.1)) =
    (fun p : (ℝ≥0 × Ω) × ℝ =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then
        w (Y p.1 + p.2) - w (Y p.1) else 0) := by
    funext p
    by_cases hp : (p.1.1 : ℝ≥0∞) ≤ τ p.1.2
    · simp [E, Set.indicator_apply, hp, R]
    · simp [E, Set.indicator_apply, hp]
  simpa only [hEq, Y] using hInt
