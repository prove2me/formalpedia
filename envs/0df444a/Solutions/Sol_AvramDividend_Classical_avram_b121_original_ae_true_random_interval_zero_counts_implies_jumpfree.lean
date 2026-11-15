-- Prove2me | solution 1 for AvramDividend.Classical.avram_b121_original_ae_true_random_interval_zero_counts_implies_jumpfree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:27:44.002857+00:00
-- url     : https://prove2.me/submissions/0181cdc9-6880-4557-8885-bb773dd2e68b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b125_original_all_zero_poisson_cutoff_counts_imply_true_jumpfree
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the genuine source conull event with empty all-negative Poisson bands at the stopped random clocks, the same physical interval is truly jumpfree. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : Ω → ℝ≥0) (hst : ∀ ω, s ω ≤ t ω)
    (hZero : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s ω) (t ω) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0) :
    ∀ᵐ ω ∂P, ∀ u : ℝ≥0, s ω < u → u ≤ t ω →
      X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by
  filter_upwards [hZero] with ω hω
  exact avram_b125_original_all_zero_poisson_cutoff_counts_imply_true_jumpfree
    X ω (s ω) (t ω) (hst ω) hω
