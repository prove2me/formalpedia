-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_clipped_predividend_gaussian_gradient_finite_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:26:06.240616+00:00
-- url     : https://prove2.me/submissions/11568d41-30a4-4689-9775-2f94c0430781

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_compact_gaussian_gradient_finite_base_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical left-reserve Gaussian gradient energy, using the original Lévy path and original dividend right-limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ Set.univ < ⊤) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    (∫⁻ p, ENNReal.ofReal ((X.σ * deriv w (U p)) ^ 2) ∂μ) < ⊤ := by
  let U : ℝ≥0 × Ω → ℝ := fun p =>
    let y := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    if y ∈ Icc δ K then y else δ
  have hU (p : ℝ≥0 × Ω) : U p ∈ Icc δ K := by
    dsimp [U]
    split_ifs with hp
    · exact hp
    · exact ⟨le_refl δ, hδK⟩
  change (∫⁻ p, ENNReal.ofReal ((X.σ * deriv w (U p)) ^ 2) ∂μ) < ⊤
  exact
    avram_p4_f3_original_compact_gaussian_gradient_finite_base_energy
      X w C hw_smooth δ K hδ hδK hK μ hμ U hU
