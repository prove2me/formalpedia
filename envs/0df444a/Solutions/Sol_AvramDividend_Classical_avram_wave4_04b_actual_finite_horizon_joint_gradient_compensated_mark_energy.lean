-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_actual_finite_horizon_joint_gradient_compensated_mark_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T20:43:37.57211+00:00
-- url     : https://prove2.me/submissions/a0570b70-0347-437d-9cd7-01e862d017a0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_time_probability_predictable_trim
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_compensated_full_negative_mark_predictable_L2_energy

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
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
       let G : ℝ≥0 × Ω → ℝ := fun p =>
          if Y p ∈ Icc (u + δ) v then deriv w (Y p) else 0
       let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
          (if Y p.1 ∈ Icc (u + δ) v then
            w (Y p.1 + p.2) - w (Y p.1) else 0) -
          (if -1 < p.2 then p.2 * G p.1 else 0)
       Measurable[𝓕.rightCont.predictable] G ∧
         (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((G p) ^ 2) ∂μ) < ⊤ ∧
         Measurable[(𝓕.rightCont.predictable).prod
           (inferInstance : MeasurableSpace ℝ)] H ∧
         (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
            ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤) := by
  obtain ⟨μ, hμ, hEq⟩ :=
    avram_wave4_04b_source_finite_horizon_time_probability_predictable_trim X T
  have hau' : a < u + δ := by linarith
  have hGrad :=
    avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
      X x D hD w a b (u + δ) v hw hau' hband hvb μ hμ
  have hMark :=
    avram_wave4_04b_controlled_compensated_full_negative_mark_predictable_L2_energy
      X x D hD w a b u v δ hw hw_cont hw_neg
        hau huv hvb hu0 hδ hδone hband μ hμ
  refine ⟨μ, hμ, hEq, ?_⟩
  dsimp only
  exact ⟨hGrad.1, hGrad.2, hMark.1, hMark.2⟩
