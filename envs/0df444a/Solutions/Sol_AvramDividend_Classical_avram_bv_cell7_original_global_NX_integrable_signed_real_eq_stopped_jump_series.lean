-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_global_NX_integrable_signed_real_eq_stopped_jump_series
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:40:54.177489+00:00
-- url     : https://prove2.me/submissions/1fc97aa2-7205-403f-8bf5-e3e13d909e77

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_jump_count_source_eq_tsum
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_global_NX_upper_clock_supported_source_unmasked

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The *real* integral of a genuinely integrable original Lévy mark source
    equals positive minus negative original stopped jump-time series. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s : ℝ≥0)
    (G : ℝ≥0 × ℝ → ℝ) (hG : Measurable G)
    (hSupport : ∀ p : ℝ≥0 × ℝ, s < p.1 → G p = 0) :
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
        (fun v : ℝ≥0 => (v, Δ v)))
    Integrable G NX →
      (∫ p, G p ∂NX) =
        (∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc 0 s then
            ENNReal.ofReal (G (v, Δ v)) else 0).toReal -
        (∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc 0 s then
            ENNReal.ofReal (-G (v, Δ v)) else 0).toReal := by
  classical
  let Δ : ℝ≥0 → ℝ := fun v =>
    X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
      (fun v : ℝ≥0 => (v, Δ v)))
  have hGp : Measurable (fun p => ENNReal.ofReal (G p)) :=
    ENNReal.measurable_ofReal.comp hG
  have hGm : Measurable (fun p => ENNReal.ofReal (-G p)) :=
    ENNReal.measurable_ofReal.comp hG.neg
  have hSuppP : ∀ p : ℝ≥0 × ℝ, s < p.1 → ENNReal.ofReal (G p) = 0 := by
    intro p hsp
    simp [hSupport p hsp]
  have hSuppM : ∀ p : ℝ≥0 × ℝ, s < p.1 → ENNReal.ofReal (-G p) = 0 := by
    intro p hsp
    simp [hSupport p hsp]
  have hCutP :
      (∫⁻ p, ENNReal.ofReal (G p) ∂NX) =
      (∫⁻ p, (if p.1 ∈ Ioc 0 s then ENNReal.ofReal (G p) else 0) ∂NX) := by
    simpa only [NX, Δ] using
      (AvramDividend.Classical.avram_bv_cell7_original_global_NX_upper_clock_supported_source_unmasked
        X ω s (fun p => ENNReal.ofReal (G p)) hGp hSuppP)
  have hCutM :
      (∫⁻ p, ENNReal.ofReal (-G p) ∂NX) =
      (∫⁻ p, (if p.1 ∈ Ioc 0 s then ENNReal.ofReal (-G p) else 0) ∂NX) := by
    simpa only [NX, Δ] using
      (AvramDividend.Classical.avram_bv_cell7_original_global_NX_upper_clock_supported_source_unmasked
        X ω s (fun p => ENNReal.ofReal (-G p)) hGm hSuppM)
  have hTsumP :
      (∫⁻ p, (if p.1 ∈ Ioc 0 s then ENNReal.ofReal (G p) else 0) ∂NX) =
      ∑' v : ℝ≥0,
        if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc 0 s then
          ENNReal.ofReal (G (v, Δ v)) else 0 := by
    simpa only [NX, Δ] using
      (AvramDividend.Classical.avram_p3_2_original_stopped_jump_count_source_eq_tsum
        X ω (Ioc 0 s) measurableSet_Ioc (fun p => ENNReal.ofReal (G p)) hGp)
  have hTsumM :
      (∫⁻ p, (if p.1 ∈ Ioc 0 s then ENNReal.ofReal (-G p) else 0) ∂NX) =
      ∑' v : ℝ≥0,
        if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc 0 s then
          ENNReal.ofReal (-G (v, Δ v)) else 0 := by
    simpa only [NX, Δ] using
      (AvramDividend.Classical.avram_p3_2_original_stopped_jump_count_source_eq_tsum
        X ω (Ioc 0 s) measurableSet_Ioc (fun p => ENNReal.ofReal (-G p)) hGm)
  change Integrable G NX → _
  intro hInt
  calc
    (∫ p, G p ∂NX) =
        (∫⁻ p, ENNReal.ofReal (G p) ∂NX).toReal -
        (∫⁻ p, ENNReal.ofReal (-G p) ∂NX).toReal :=
          MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hInt
    _ = _ := by rw [hCutP, hCutM, hTsumP, hTsumM]
