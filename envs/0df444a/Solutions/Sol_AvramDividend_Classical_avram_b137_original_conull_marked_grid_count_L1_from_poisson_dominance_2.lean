-- Prove2me | solution 2 for AvramDividend.Classical.avram_b137_original_conull_marked_grid_count_L1_from_poisson_dominance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:33:30.396862+00:00
-- url     : https://prove2.me/submissions/681edae9-69ed-41ae-a3ba-c6c0d2ebc4dc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hBound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (J : Ω → Finset ℕ)
    (hJdom : ∀ᵐ ω ∂P, ((J ω).card : ℝ≥0∞) ≤
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ))) :
    (∫⁻ ω, ((J ω).card : ℝ≥0∞) ∂P) < ⊤ := by
  have hPoisson :=
    avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
      X hFinite n σ hBound
  exact lt_of_le_of_lt (lintegral_mono_ae hJdom) hPoisson
