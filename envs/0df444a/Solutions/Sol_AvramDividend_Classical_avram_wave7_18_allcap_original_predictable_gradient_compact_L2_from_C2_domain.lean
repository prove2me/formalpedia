-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_allcap_original_predictable_gradient_compact_L2_from_C2_domain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:24:01.484213+00:00
-- url     : https://prove2.me/submissions/e91f0eab-6707-47ba-bb1b-1bde7daa969e

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
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b u v : ℝ)
    (ha : 0 < a) (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hband : ∀ y : ℝ, y ∈ Ioo a b → ENNReal.ofReal y < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    Measurable[𝓕.rightCont.predictable] H ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((H p) ^ 2) ∂μ) < ⊤ := by
  have hStrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hC2 : ContDiffOn ℝ 2 w (Ioo a b) :=
    hw_smooth.mono (by
      intro y hy
      exact ⟨lt_trans ha hy.1, hband y hy⟩)
  exact avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
    X x D hStrat w a b u v hC2 hau huv hvb μ hμ
