-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_gauss14_original_negative_band_signed_shift_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:21:11.35286+00:00
-- url     : https://prove2.me/submissions/3e0e376c-10f9-4842-94f7-72848a93cbfc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_generic_negative_mark_window_integral_formula
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_arbitrary_shift_weighted_jump_mass_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The signed negative original future jump mass is exactly that of the shifted original path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : ∀ z ∈ B, z ≤ 0) :
    let Y := fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω
    let μ : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
        (fun u : ℝ≥0 => (u, Y u - Function.leftLim Y u))
    let ν : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    (∫ p in (Ioc s (s + T) ×ˢ B), p.2 ∂ν) =
      (∫ p in (Ioc 0 T ×ˢ B), p.2 ∂μ) := by
  classical
  dsimp only
  let Y : ℝ≥0 → ℝ := fun u => X.X (s + u) ω - X.X s ω
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
      (fun u : ℝ≥0 => (u, Y u - Function.leftLim Y u))
  let ν : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  change (∫ p in (Ioc s (s + T) ×ˢ B), p.2 ∂ν) =
    (∫ p in (Ioc 0 T ×ˢ B), p.2 ∂μ)
  let g : ℝ → ℝ≥0∞ := fun z => if z ∈ B then ENNReal.ofReal (-z) else 0
  have hg : Measurable g := by
    classical
    dsimp [g]
    exact Measurable.ite hB
      (ENNReal.measurable_ofReal.comp measurable_neg)
      (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ≥0∞)))
  have hshift :
      (∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂μ) =
      (∫⁻ p : ℝ≥0 × ℝ,
        if s < p.1 ∧ p.1 ≤ s + T then g p.2 else 0 ∂ν) := by
    exact avram_mix_gauss14_original_arbitrary_shift_weighted_jump_mass_exact
      X ω s T g hg
  calc
    (∫ p in (Ioc s (s + T) ×ˢ B), p.2 ∂ν) =
        -((∫⁻ p : ℝ≥0 × ℝ,
          if s < p.1 ∧ p.1 ≤ s + T then g p.2 else 0 ∂ν).toReal) :=
      avram_mix_gauss14_generic_negative_mark_window_integral_formula
        ν s (s + T) B hB hNeg
    _ = -((∫⁻ p : ℝ≥0 × ℝ,
          if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂μ).toReal) := by
      rw [hshift]
    _ = (∫ p in (Ioc 0 T ×ˢ B), p.2 ∂μ) :=
      (avram_mix_gauss14_generic_negative_mark_window_integral_formula
        μ 0 T B hB hNeg).symm
