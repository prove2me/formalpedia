-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_original_controlled_gradient_predictable_MemLp_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:23:30.858977+00:00
-- url     : https://prove2.me/submissions/dd12233d-ece6-46b5-8a2d-3d1dacafe23e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
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
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    @MemLp (ℝ≥0 × Ω) ℝ (𝓕.rightCont.predictable)
      _ _ G 2 μ := by
  dsimp only
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let G : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then deriv w (Y p) else 0
  change MemLp G 2 μ
  have hG :=
    avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
      X x D hD w a b u v hw hau huv hvb μ hμ
  have hmeas : Measurable G := hG.1
  have henergy :
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((G p) ^ 2) ∂μ) < ⊤ :=
    hG.2
  have hSq : Integrable (fun p : ℝ≥0 × Ω => G p ^ 2) μ := by
    refine ⟨(hmeas.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun p : ℝ≥0 × Ω => sq_nonneg (G p)))]
    exact henergy
  exact (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hSq
