-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian17_original_masked_gradient_MemLp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:18:50.785231+00:00
-- url     : https://prove2.me/submissions/f80381b8-960b-42a4-8f51-0cd46e5f9faa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    MemLp G 2 μ := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then deriv w (Y p) else 0
  let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
  have hSource : Measurable G ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((G p) ^ 2) ∂μ) < ⊤ :=
    avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
      X x D hD w a b u v hw hau huv hvb μ hμ
  rcases hSource with ⟨hG, hEnergy⟩
  have hSquareMeas : AEStronglyMeasurable (fun p => (G p) ^ 2) μ :=
    (hG.pow_const 2).aestronglyMeasurable
  have hSquareNonneg : 0 ≤ᵐ[μ] (fun p => (G p) ^ 2) :=
    Filter.Eventually.of_forall (fun p => sq_nonneg (G p))
  have hSquareInt : Integrable (fun p => (G p) ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hSquareMeas hSquareNonneg).mp
      (ne_of_lt hEnergy)
  exact (memLp_two_iff_integrable_sq hG.aestronglyMeasurable).2 hSquareInt
