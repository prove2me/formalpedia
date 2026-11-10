-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_gauss14_original_negative_band_integral_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:50:36.283039+00:00
-- url     : https://prove2.me/submissions/95a608da-a8f4-4d01-8b32-dfb8a57f6499

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_negative_integral_eq_neg_lintegral_toReal
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_general_mark_lintegral_filtration_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original-filtration signed negative-band jump integral measurability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : ∀ z ∈ B, z ≤ 0) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ∫ p in (Ioc (0 : ℝ≥0) T ×ˢ B), p.2 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by
  classical
  let J : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let S : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) T ×ˢ B
  let g : ℝ → ℝ≥0∞ := fun z => if z ∈ B then ENNReal.ofReal (-z) else 0
  have hS : MeasurableSet S := measurableSet_Ioc.prod hB
  have hg : Measurable g := by
    dsimp [g]
    exact Measurable.ite hB
      (ENNReal.measurable_ofReal.comp measurable_neg)
      (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ≥0∞)))
  have hm : Measurable[𝓕 T] (fun ω =>
      ∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂J ω) :=
    avram_mix_gauss14_original_general_mark_lintegral_filtration_measurable X T g hg
  have hEq (ω : Ω) :
      (∫ p in S, p.2 ∂J ω) =
      -((∫⁻ p : ℝ≥0 × ℝ,
          if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂J ω).toReal) := by
    have hneg := avram_mix_gauss14_negative_integral_eq_neg_lintegral_toReal
      (J ω) S hS (fun p : ℝ≥0 × ℝ => p.2) measurable_snd
      (by intro p hp; exact hNeg p.2 hp.2)
    rw [hneg]
    congr 1
    rw [← lintegral_indicator hS]
    congr 1
    apply lintegral_congr
    intro p
    by_cases ht : 0 < p.1 ∧ p.1 ≤ T
    · by_cases hb : p.2 ∈ B
      · simp [S, g, Set.indicator, Set.mem_prod, Set.mem_Ioc, ht, hb]
      · simp [S, g, Set.indicator, Set.mem_prod, Set.mem_Ioc, ht, hb]
    · simp [S, g, Set.indicator, Set.mem_prod, Set.mem_Ioc, ht]
  have hR : Measurable[𝓕 T] (fun ω =>
      -((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂J ω).toReal)) :=
    (ENNReal.measurable_toReal.comp hm).neg
  change Measurable[𝓕 T] (fun ω => ∫ p in S, p.2 ∂J ω)
  have hFun : (fun ω : Ω => ∫ p in S, p.2 ∂J ω) =
      (fun ω => -((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂J ω).toReal)) := by
    funext ω
    exact hEq ω
  rw [hFun]
  exact hR
