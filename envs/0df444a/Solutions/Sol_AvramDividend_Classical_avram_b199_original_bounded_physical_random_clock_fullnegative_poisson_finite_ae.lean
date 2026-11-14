-- Prove2me | solution 1 for AvramDividend.Classical.avram_b199_original_bounded_physical_random_clock_fullnegative_poisson_finite_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:48:48.398436+00:00
-- url     : https://prove2.me/submissions/b9bbb40b-67d2-45c6-936d-004a40b2a1a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b198_original_fullnegative_bounded_random_clock_poisson_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b195_original_fullnegative_poisson_count_finite_ae_from_source_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Under finite original negative Levy activity, the complete genuine original marked Poisson count up to any bounded measurable random physical clock is finite almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσ : Measurable σ)
    (hBound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ)) < ⊤ := by
  have hMeas :=
    avram_b198_original_fullnegative_bounded_random_clock_poisson_count_measurable
      X σ hσ
  exact avram_b195_original_fullnegative_poisson_count_finite_ae_from_source_L1
    X hFinite n σ hBound hMeas.aemeasurable
