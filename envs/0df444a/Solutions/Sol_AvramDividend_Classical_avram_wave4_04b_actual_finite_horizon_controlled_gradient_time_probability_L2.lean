-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_actual_finite_horizon_controlled_gradient_time_probability_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T20:34:37.630204+00:00
-- url     : https://prove2.me/submissions/b23008d2-c2a7-4caf-a4be-b0bbaf59b6aa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_time_probability_predictable_trim
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
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
       let H : ℝ≥0 × Ω → ℝ := fun p =>
          if Y p ∈ Icc u v then deriv w (Y p) else 0
       Measurable[𝓕.rightCont.predictable] H ∧
         (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((H p) ^ 2) ∂μ) < ⊤) := by
  obtain ⟨μ, hμ, hEq⟩ :=
    avram_wave4_04b_source_finite_horizon_time_probability_predictable_trim X T
  refine ⟨μ, hμ, hEq, ?_⟩
  exact avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
    X x D hD w a b u v hw hau huv hvb μ hμ
