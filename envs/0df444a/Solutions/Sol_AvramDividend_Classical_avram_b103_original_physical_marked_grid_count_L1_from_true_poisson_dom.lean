-- Prove2me | solution 1 for AvramDividend.Classical.avram_b103_original_physical_marked_grid_count_L1_from_true_poisson_dom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:29:23.530952+00:00
-- url     : https://prove2.me/submissions/b4fa644d-e8b7-4230-8251-743324975986

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Physical original marked-cell cardinality is L1 dominated by the true stopped negative-jump Poisson source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hBound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (J : Ω → Finset ℕ)
    (hJdom : ∀ ω : Ω, ((J ω).card : ℝ≥0∞) ≤
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ))) :
    (∫⁻ ω, ((J ω).card : ℝ≥0∞) ∂P) < ⊤ := by
  apply lt_of_le_of_lt ?_
    (avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
      X hFinite n σ hBound)
  exact lintegral_mono (fun ω => hJdom ω)
