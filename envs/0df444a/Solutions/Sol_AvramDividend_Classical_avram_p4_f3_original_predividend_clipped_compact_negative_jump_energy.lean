-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_predividend_clipped_compact_negative_jump_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:22:00.752525+00:00
-- url     : https://prove2.me/submissions/bbf28faa-1e8d-4ef4-b39c-e7a9478edc55

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_compact_negative_jump_finite_base_quadratic_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The literal original pre-payment reserve, clipped into the strict compact band, has finite source Lévy mark energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ Set.univ < ⊤) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    (∫⁻ p, ∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal ((w (U p + z) - w (U p)) ^ 2) ∂X.ν ∂μ) < ⊤ := by
  let U : ℝ≥0 × Ω → ℝ := fun p =>
    let y := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    if y ∈ Icc δ K then y else δ
  have hU (p : ℝ≥0 × Ω) : U p ∈ Icc δ K := by
    dsimp [U]
    split_ifs with hp
    · exact hp
    · exact ⟨le_refl δ, hδK⟩
  change (∫⁻ p, ∫⁻ z in Iio (0 : ℝ),
    ENNReal.ofReal ((w (U p + z) - w (U p)) ^ 2) ∂X.ν ∂μ) < ⊤
  exact
    avram_p4_f3_original_compact_negative_jump_finite_base_quadratic_energy
      X w C hw_cont hw_neg hw_smooth δ K hδ hδK hK
      μ hμ U hU
