-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_mark_thinning_variance_vanishes_under_source_isometry_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:52:43.47693+00:00
-- url     : https://prove2.me/submissions/ae40eba7-cc24-4ce8-a329-a85e6b85e04d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_L2_thinning_tail_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the original source, any sequence of compensated small-jump
approximants satisfying the explicit predictable variance bound has
vanishing second moment as the negative mark bands shrink to empty. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (Y : ℕ → Ω → ℝ)
    (hYbound : ∀ n,
      (∫⁻ ω, ENNReal.ofReal ((Y n ω)^2) ∂P) ≤
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ({r : ((ℝ≥0 × Ω) × ℝ) | r.2 ∈ B n}).indicator
          (fun r : ((ℝ≥0 × Ω) × ℝ) =>
            ENNReal.ofReal ((g r.1 * r.2)^2)) p
        ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
          μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))) :
    Tendsto (fun n : ℕ =>
      (∫⁻ ω, ENNReal.ofReal ((Y n ω)^2) ∂P)) atTop (𝓝 0) := by
  have htail :=
    avram_p4_b_smalljump_original_predictable_linear_L2_thinning_tail_zero
      X μ g hgm hgL2 B hBm hBanti hBempty
  exact Filter.Tendsto.squeeze' tendsto_const_nhds htail
    (Filter.Eventually.of_forall (fun _ => bot_le))
    (Filter.Eventually.of_forall hYbound)
