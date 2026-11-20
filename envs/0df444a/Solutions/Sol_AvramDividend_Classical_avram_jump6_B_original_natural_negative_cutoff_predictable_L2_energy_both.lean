-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_natural_negative_cutoff_predictable_L2_energy_both
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:54:15.671506+00:00
-- url     : https://prove2.me/submissions/d5532b00-dff5-4f12-818c-773c7af459c7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_L2_thinning_tail_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_product_eLpNorm_tail_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_canonical_negative_mark_bands_antitone_empty
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤) :
    let B : ℕ → Set ℝ := fun n =>
      Ioo (-(1 / ((n : ℝ) + 1))) (0 : ℝ);
    Tendsto (fun n : ℕ => (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
      ({r : ((ℝ≥0 × Ω) × ℝ) | r.2 ∈ B n}).indicator
        (fun r => ENNReal.ofReal ((g r.1 * r.2)^2)) p
      ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
        μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))) atTop (𝓝 (0 : ℝ≥0∞)) ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Tendsto (fun n : ℕ =>
        eLpNorm
          (({r : ((ℝ≥0 × Ω) × ℝ) | r.2 ∈ B n}).indicator
            (fun r : ((ℝ≥0 × Ω) × ℝ) => g r.1 * r.2))
          (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))
        atTop (𝓝 (0 : ℝ≥0∞)))
 := by
  classical
  let B : ℕ → Set ℝ := fun n =>
    Ioo (-(1 / ((n : ℝ) + 1))) (0 : ℝ)
  have hBm : ∀ n, MeasurableSet (B n) := by
    intro n
    exact measurableSet_Ioo
  have hBand : Antitone B ∧ (⋂ n, B n) = ∅ := by
    simpa only [B, Nat.cast_add, Nat.cast_one, neg_div] using
      avram_p4_b_smalljump_canonical_negative_mark_bands_antitone_empty
  constructor
  · exact avram_p4_b_smalljump_original_predictable_linear_L2_thinning_tail_zero
      X μ g hgm hgL2 B hBm hBand.1 hBand.2
  · exact avram_p4_b_smalljump_original_predictable_linear_product_eLpNorm_tail_zero
      X μ g hgm hgL2 B hBm hBand.1 hBand.2
