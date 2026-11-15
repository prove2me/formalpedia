-- Prove2me | solution 1 for AvramDividend.Classical.avram_b137_original_conull_marked_grid_count_L1_from_poisson_dominance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:32:53.908443+00:00
-- url     : https://prove2.me/submissions/d748bbf6-154f-4277-b4d0-1bbf6d315f3e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Physical original marked-cell cardinality is L1 when dominated almost everywhere by the true stopped source negative Poisson jump count. -/
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
  apply lt_of_le_of_lt ?_
    (avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
      X hFinite n σ hBound)
  exact lintegral_mono_ae hJdom
