-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump12_original_initial_event_masked_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T18:22:01.393931+00:00
-- url     : https://prove2.me/submissions/1b5d4d85-3ca9-476d-945b-4ce944cdd7b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-- Initial-event clock masking commutes with the original physical negative-jump
compensator because the real-time compensator has no atom at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (A : Set Ω) (σ : Ω → ℝ≥0)
    (H : Ω → ℝ≥0 → ℝ → ℝ) :
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    ∀ ω,
      (∫ t, ∫ z, (if t ≤ A.indicator σ ω then H ω t z else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT) =
      A.indicator (fun ξ =>
        ∫ t, ∫ z, (if t ≤ σ ξ then H ξ t z else 0)
          ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT) ω := by
  intro μT ω
  by_cases hA : ω ∈ A
  · simp [Set.indicator, hA]
  · have hTime0 : μT {(0 : ℝ≥0)} = 0 := by
      change (((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal) {(0 : ℝ≥0)} = 0
      rw [Measure.map_apply measurable_real_toNNReal
        (measurableSet_singleton (0 : ℝ≥0))]
      rw [Measure.restrict_apply
        (measurable_real_toNNReal (measurableSet_singleton (0 : ℝ≥0)))]
      have hsub :
          (Real.toNNReal ⁻¹' {(0 : ℝ≥0)}) ∩
            Icc 0 (T : ℝ) ⊆ {(0 : ℝ)} := by
        intro x hx
        have hx0 : (0 : ℝ) ≤ x := hx.2.1
        have hval : (x.toNNReal : ℝ) = x := Real.coe_toNNReal x hx0
        have hz : x.toNNReal = (0 : ℝ≥0) := hx.1
        exact Set.mem_singleton_iff.mpr (by
          calc
            x = (x.toNNReal : ℝ) := hval.symm
            _ = 0 := congrArg (fun y : ℝ≥0 => (y : ℝ)) hz)
      exact le_antisymm ((measure_mono hsub).trans (by simp)) bot_le
    have hSet : {t : ℝ≥0 | t ≤ (0 : ℝ≥0)} = {(0 : ℝ≥0)} := by
      ext t
      simp [le_zero_iff]
    have hNull : μT {t : ℝ≥0 | t ≤ (0 : ℝ≥0)} = 0 := by
      simpa only [hSet] using hTime0
    have hAE : ∀ᵐ t ∂μT, ¬t ≤ (0 : ℝ≥0) := by
      apply (ae_iff).2
      simpa only [not_not] using hNull
    have hZero :
        (∫ t, ∫ z, (if t ≤ (0 : ℝ≥0) then H ω t z else 0)
          ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hAE] with t ht
      simp [ht]
    simpa [Set.indicator, hA] using hZero
