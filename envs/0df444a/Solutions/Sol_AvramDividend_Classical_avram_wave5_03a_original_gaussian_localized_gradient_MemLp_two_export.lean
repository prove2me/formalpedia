-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_original_gaussian_localized_gradient_MemLp_two_export
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:42:11.677527+00:00
-- url     : https://prove2.me/submissions/e4019d97-6d58-4c7d-9102-00063aa5a823

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_controlled_gradient_predictable_MemLp_two

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
    (ρ : ℝ≥0 × Ω → ℝ)
    (hρ : Measurable[𝓕.rightCont.predictable] ρ)
    (hρbdd : ∀ p, |ρ p| ≤ 1)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    @MemLp (ℝ≥0 × Ω) ℝ (𝓕.rightCont.predictable)
      _ _ (fun p => ρ p * (X.σ * G p)) 2 μ := by
  dsimp only
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let G : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then deriv w (Y p) else 0
  change MemLp (fun p => ρ p * (X.σ * G p)) 2 μ
  have henergy :=
    avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
      X x D hD w a b u v hw hau huv hvb μ hμ
  have hGmeas : Measurable G := henergy.1
  have hG : MemLp G 2 μ :=
    avram_wave4_04b_original_controlled_gradient_predictable_MemLp_two
      X x D hD w a b u v hw hau huv hvb μ hμ
  have hσ : MemLp (fun p => X.σ * G p) 2 μ := hG.const_mul X.σ
  have hρmeas : Measurable ρ := hρ
  have hprod : Measurable (fun p => ρ p * (X.σ * G p)) :=
    hρmeas.mul (measurable_const.mul hGmeas)
  have hdom : ∀ p : ℝ≥0 × Ω,
      ‖ρ p * (X.σ * G p)‖ ≤ ‖X.σ * G p‖ := by
    intro p
    simpa only [Real.norm_eq_abs, abs_mul, one_mul] using
      (mul_le_mul_of_nonneg_right (hρbdd p) (abs_nonneg (X.σ * G p)))
  exact hσ.of_le hprod.aestronglyMeasurable
    (Filter.Eventually.of_forall hdom)