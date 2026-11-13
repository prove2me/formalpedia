-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB174_original_gaussian_uniform_localtime_small_ball_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:43:47.643102+00:00
-- url     : https://prove2.me/submissions/ab6cfcd8-574d-49c8-bc15-56594f290bc8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB175_original_gaussian_controlled_localtime_density
import Theorems.Thm_AvramDividend_Classical_avram_gbB176_bounded_occupation_density_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_gbB177_real_symmetric_interval_volume
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ L : ℝ≥0, ∀ (y ε : ℝ),
      0 < ε → ε ≤ 1 →
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        abs (x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω - y) < ε} ≤
        ENNReal.ofReal ((L : ℝ) * ε) := by
  have hocc := avram_gbB175_original_gaussian_controlled_localtime_density
    X hBV hν x b D hD n ρ
  filter_upwards [hocc] with ω hω
  obtain ⟨ℓ, B, hB, hℓ⟩ := hω
  refine ⟨2 * B, ?_⟩
  intro y ε hε hε1
  have hmass := hℓ y ε hε hε1
  have hbound :=
    avram_gbB176_bounded_occupation_density_lintegral
      ℓ (B : ℝ≥0∞) (y - ε) (y + ε) hB
  have hlen := avram_gbB177_real_symmetric_interval_volume y ε
  calc
    volume {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
      abs (x + X.X (Real.toNNReal t) ω -
        rightLimit D (Real.toNNReal t) ω - y) < ε}
        ≤ ∫⁻ z in Ioo (y - ε) (y + ε), ℓ z ∂volume := hmass
    _ ≤ (B : ℝ≥0∞) * volume (Ioo (y - ε) (y + ε)) := hbound
    _ = ENNReal.ofReal (((2 * B : ℝ≥0) : ℝ) * ε) := by
      rw [hlen]
      have hn : (0 : ℝ) ≤ (B : ℝ) := B.coe_nonneg
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hn]
      congr 1
      push_cast
      ring
