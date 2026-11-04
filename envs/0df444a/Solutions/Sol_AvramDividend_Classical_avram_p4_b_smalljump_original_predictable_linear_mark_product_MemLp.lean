-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_linear_mark_product_MemLp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:21:21.620028+00:00
-- url     : https://prove2.me/submissions/019f2dd9-67c1-461c-8a1a-b16ebcd54044

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_L2_linear_mark_factorisation
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_real_product_L2_square_to_eNorm_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original predictable linear negative mark belongs to L2 on the
actual physical predictable clock times its genuine source Lévy band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤)
    (B : Set ℝ)
    (hBmoment : (∫⁻ z in B,
      ENNReal.ofReal (z^2) ∂X.ν) < ⊤)
    (hνs : SFinite (X.ν.restrict B)) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      MemLp (fun p : ((ℝ≥0 × Ω) × ℝ) => g p.1 * p.2)
        (2 : ℝ≥0∞) (μ.prod (X.ν.restrict B))) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : SFinite (X.ν.restrict B) := hνs
  let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => g p.1 * p.2
  have hGm : Measurable G :=
    (hgm.comp measurable_fst).mul measurable_snd
  have hSquare :
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal ((G p)^2) ∂(μ.prod (X.ν.restrict B))) < ⊤ := by
    have hm : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
        ENNReal.ofReal ((G p)^2)) :=
      ENNReal.measurable_ofReal.comp (hGm.pow_const 2)
    rw [MeasureTheory.lintegral_prod _ hm.aemeasurable]
    exact (avram_p4_b_smalljump_original_predictable_L2_linear_mark_factorisation
      X μ g hgm hgL2 B hBmoment).2
  have hEnergy :
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ‖G p‖ₑ ^ (2 : ℝ) ∂(μ.prod (X.ν.restrict B))) < ⊤ :=
    avram_wave6_02_real_product_L2_square_to_eNorm_energy
      (μ.prod (X.ν.restrict B)) G hSquare
  change MemLp G (2 : ℝ≥0∞) (μ.prod (X.ν.restrict B))
  constructor
  · exact hGm.aestronglyMeasurable
  · apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).2
    simpa using hEnergy
