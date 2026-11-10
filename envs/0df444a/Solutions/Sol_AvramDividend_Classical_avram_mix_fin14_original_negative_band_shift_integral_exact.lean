-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin14_original_negative_band_shift_integral_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:10:06.955081+00:00
-- url     : https://prove2.me/submissions/32cf8281-2989-4c82-b3bc-f1d588b4d4a7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_negative_integral_eq_neg_lintegral_toReal
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_arbitrary_shift_weighted_jump_mass_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Translate the signed negative-band real jump integral along the original sample path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B) (hNeg : ∀ z ∈ B, z ≤ 0) :
    (∫ p in (Ioc (0 : ℝ≥0) T ×ˢ B), p.2 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ (X.X (s + u) ω - X.X s ω) -
          Function.leftLim (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, (X.X (s + u) ω - X.X s ω) -
          Function.leftLim (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u)))) =
    (∫ p in (Ioc s (s + T) ×ˢ B), p.2 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by
  classical
  let Y : ℝ≥0 → ℝ := fun u => X.X (s + u) ω - X.X s ω
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
      (fun u => (u, Y u - Function.leftLim Y u))
  let ν : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let S0 : Set (ℝ≥0 × ℝ) := Ioc 0 T ×ˢ B
  let Ss : Set (ℝ≥0 × ℝ) := Ioc s (s + T) ×ˢ B
  let g : ℝ → ℝ≥0∞ := fun z => if z ∈ B then ENNReal.ofReal (-z) else 0
  have hS0 : MeasurableSet S0 := measurableSet_Ioc.prod hB
  have hSs : MeasurableSet Ss := measurableSet_Ioc.prod hB
  have hg : Measurable g :=
    Measurable.ite hB (ENNReal.measurable_ofReal.comp measurable_neg) measurable_const
  have hN0 : (∫ p in S0, p.2 ∂μ) =
      -((∫⁻ p in S0, ENNReal.ofReal (-p.2) ∂μ).toReal) :=
    avram_mix_gauss14_negative_integral_eq_neg_lintegral_toReal
      μ S0 hS0 (fun p : ℝ≥0 × ℝ => p.2) measurable_snd
      (by intro p hp; exact hNeg p.2 hp.2)
  have hNs : (∫ p in Ss, p.2 ∂ν) =
      -((∫⁻ p in Ss, ENNReal.ofReal (-p.2) ∂ν).toReal) :=
    avram_mix_gauss14_negative_integral_eq_neg_lintegral_toReal
      ν Ss hSs (fun p : ℝ≥0 × ℝ => p.2) measurable_snd
      (by intro p hp; exact hNeg p.2 hp.2)
  have hL0 :
      (∫⁻ p in S0, ENNReal.ofReal (-p.2) ∂μ) =
      (∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂μ) := by
    rw [← lintegral_indicator hS0]
    apply lintegral_congr
    intro p
    simp [S0, g, Set.indicator, Set.mem_prod, Set.mem_Ioc, ite_and]
  have hLs :
      (∫⁻ p in Ss, ENNReal.ofReal (-p.2) ∂ν) =
      (∫⁻ p : ℝ≥0 × ℝ,
        if s < p.1 ∧ p.1 ≤ s + T then g p.2 else 0 ∂ν) := by
    rw [← lintegral_indicator hSs]
    apply lintegral_congr
    intro p
    simp [Ss, g, Set.indicator, Set.mem_prod, Set.mem_Ioc, ite_and]
  have hShift :=
    avram_mix_gauss14_original_arbitrary_shift_weighted_jump_mass_exact
      X ω s T g hg
  change (∫ p in S0, p.2 ∂μ) = (∫ p in Ss, p.2 ∂ν)
  rw [hN0, hNs, hL0, hLs, hShift]
