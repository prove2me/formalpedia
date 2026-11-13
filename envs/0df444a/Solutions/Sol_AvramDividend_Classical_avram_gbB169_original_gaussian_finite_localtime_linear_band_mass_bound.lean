-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB169_original_gaussian_finite_localtime_linear_band_mass_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:36:33.683536+00:00
-- url     : https://prove2.me/submissions/6aa41763-8c44-420f-9b51-0bfaa8480e5e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB174_original_gaussian_uniform_localtime_small_ball_bound
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
    ∀ᵐ ω ∂P, ∃ L : ℝ≥0, ∀ k : ℕ,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        abs (x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω - b) <
            (1 : ℝ) / ((k : ℝ) + 1)} ≤
        ENNReal.ofReal ((L : ℝ) / ((k : ℝ) + 1)) := by
  have hsmall :=
    avram_gbB174_original_gaussian_uniform_localtime_small_ball_bound
      X hBV hν x b D hD n ρ
  filter_upwards [hsmall] with ω hω
  obtain ⟨L, hL⟩ := hω
  refine ⟨L, ?_⟩
  intro k
  have hepos : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by positivity
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hele : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).2
    linarith
  convert hL b ((1 : ℝ) / ((k : ℝ) + 1)) hepos hele using 1
  simp only [div_eq_mul_inv, one_mul]
