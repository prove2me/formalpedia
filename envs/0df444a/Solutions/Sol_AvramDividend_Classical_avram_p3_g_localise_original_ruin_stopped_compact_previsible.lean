-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_ruin_stopped_compact_previsible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:29:11.642799+00:00
-- url     : https://prove2.me/submissions/bf72ba26-a9e4-437b-b88a-6339617dc685

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_real_truncated_ruin_nnreal_stopping
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual finite ruin-stop and closed reserve band define a predictable
pre-ruin compact localisation, including the terminal stopping instant. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (a b : ℝ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    (∀ ω, τ ω ≤ T) ∧
    IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) ∧
    MeasurableSet[𝓕.rightCont.predictable] E ∧
    (∀ p ∈ E, Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b) ∧
    (∀ p ∈ E, p.1 ≤ T) := by
  classical
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  have hclock := avram_p3_bv_original_real_truncated_ruin_nnreal_stopping
    X x D hD T
  have hpred := avram_wave3_04_inclusiveSurvival_stronglyPredictable
    (fun ω : Ω => (τ ω : ℝ≥0∞)) hclock.2
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hm : Measurable (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) then (1 : ℝ) else 0) :=
    (show StronglyMeasurable (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) then (1 : ℝ) else 0)
      from hpred).measurable
  have hsurvive : MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞)} := by
    have hEq : ({p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞)} : Set (ℝ≥0 × Ω)) =
        (fun p : ℝ≥0 × Ω =>
          if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) then (1 : ℝ) else 0) ⁻¹'
          ({1} : Set ℝ) := by
      ext p
      simp
    rw [hEq]
    exact (measurableSet_singleton (1 : ℝ)).preimage hm
  have hband : MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω | Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b} :=
    avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
      X x D hD a b
  have hEm : MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b} := by
    change MeasurableSet[𝓕.rightCont.predictable]
      ({p : ℝ≥0 × Ω | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞)} ∩
       {p : ℝ≥0 × Ω | Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b})
    exact hsurvive.inter hband
  refine ⟨hclock.1, hclock.2, hEm, ?_, ?_⟩
  · intro p hp
    exact hp.2
  · intro p hp
    exact (ENNReal.coe_le_coe.mp hp.1).trans (hclock.1 p.2)
