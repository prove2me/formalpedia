-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_actual_stopped_gradient_gaussian_bracket_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:27:23.997693+00:00
-- url     : https://prove2.me/submissions/376f81b3-1efb-4a5a-9916-0be7e6682de7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_rightcont_predictable_bracket_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original spectrally negative Lévy Gaussian source σ·w'(Y_{s-}) has
an adapted squared bracket on the *same* right-continuous stopping filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (μtime : Measure ℝ≥0) [SFinite μtime] :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    Adapted 𝓕.rightCont (fun t ω =>
      ∫ s in Ioc (0 : ℝ≥0) t, (G (s, ω)) ^ 2 ∂μtime) := by
  exact avram_ubv_gaussian10_rightcont_predictable_bracket_adapted
    X _
    (avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
      X x D hD w a b u v hw hau huv hvb μ hμ).1 μtime
