-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_original_finite_horizon_controlled_gradient_actual_product_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T20:51:38.375631+00:00
-- url     : https://prove2.me/submissions/4f860f53-08b0-45c4-a20d-749e6ee737d9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    Measurable[𝓕.rightCont.predictable] G ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((G p) ^ 2)
        ∂((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)) < ⊤ := by
  dsimp only
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let G : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then deriv w (Y p) else 0
  change Measurable[𝓕.rightCont.predictable] G ∧
    (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((G p) ^ 2)
      ∂((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)) < ⊤
  obtain ⟨μ, hμ, _, hInt⟩ :=
    avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability X T
  have hsource :=
    avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
      X x D hD w a b u v hw hau huv hvb μ hμ
  have hG : Measurable[𝓕.rightCont.predictable] G := hsource.1
  have hG2 :
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((G p) ^ 2) ∂μ) < ⊤ :=
    hsource.2
  refine ⟨hG, ?_⟩
  have hf : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => ENNReal.ofReal ((G p) ^ 2)) :=
    (hG.pow_const 2).ennreal_ofReal
  rw [← hInt _ hf]
  exact hG2
