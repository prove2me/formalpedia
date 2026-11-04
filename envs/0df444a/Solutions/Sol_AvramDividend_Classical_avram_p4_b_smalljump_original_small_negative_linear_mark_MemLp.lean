-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_small_negative_linear_mark_MemLp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:29:20.233461+00:00
-- url     : https://prove2.me/submissions/fc222c9f-e240-408a-bab4-6b3f47d96f0e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_small_negative_jump_square_moment
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_mark_product_MemLp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual bounded-negative small-jump linear mark is square-integrable
on its genuine original predictable Lévy product clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      MemLp (fun p : ((ℝ≥0 × Ω) × ℝ) => g p.1 * p.2)
        (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))) := by
  letI : SFinite (X.ν.restrict (Iio (0 : ℝ))) :=
    levy_negative_jump_measure_sFinite X
  have hνs : SFinite (X.ν.restrict (Ioo (-1 : ℝ) 0)) := by
    have hsub : Ioo (-1 : ℝ) 0 ⊆ Iio 0 :=
      fun _ hz => hz.2
    have heq : X.ν.restrict (Ioo (-1 : ℝ) 0) =
        (X.ν.restrict (Iio (0 : ℝ))).restrict (Ioo (-1 : ℝ) 0) :=
      (Measure.restrict_restrict_of_subset hsub).symm
    rw [heq]
    infer_instance
  exact avram_p4_b_smalljump_original_predictable_linear_mark_product_MemLp
    X μ g hgm hgL2 (Ioo (-1 : ℝ) 0)
    (finite_small_negative_jump_square_moment X.ν X.ν_integrable) hνs
