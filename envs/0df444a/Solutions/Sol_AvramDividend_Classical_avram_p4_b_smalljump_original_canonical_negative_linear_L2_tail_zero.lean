-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_canonical_negative_linear_L2_tail_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:11:25.577843+00:00
-- url     : https://prove2.me/submissions/e631b28f-20ed-496f-979e-fc3d4b2a49cd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_L2_thinning_tail_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_canonical_negative_mark_bands_antitone_empty
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual source linear compensated small-jump integrand has vanishing
predictable quadratic energy in the canonical infinite-activity near-zero
negative bands (-1/(n+1),0), without requiring finite first moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤) :
    Tendsto (fun n : ℕ =>
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ({r : ((ℝ≥0 × Ω) × ℝ) |
          r.2 ∈ Ioo (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ)) (0 : ℝ)}).indicator
          (fun r : ((ℝ≥0 × Ω) × ℝ) =>
            ENNReal.ofReal ((g r.1 * r.2)^2)) p
        ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
          μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))) atTop (𝓝 0) := by
  have ⟨hanti, hempty⟩ :=
    avram_p4_b_smalljump_canonical_negative_mark_bands_antitone_empty
  exact avram_p4_b_smalljump_original_predictable_linear_L2_thinning_tail_zero
    X μ g hgm hgL2
    (fun n : ℕ => Ioo (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ)) (0 : ℝ))
    (fun _ => measurableSet_Ioo) hanti hempty
