-- Prove2me | solution 1 for AvramDividend.Classical.avram_b126_original_zero_all_negative_counts_iff_true_jumpfree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:27:58.163271+00:00
-- url     : https://prove2.me/submissions/5b42832e-2492-4b93-b59b-f2b501815f0a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b125_original_all_zero_poisson_cutoff_counts_imply_true_jumpfree
import Theorems.Thm_AvramDividend_Classical_avram_b123_original_actual_jumpfree_implies_every_negative_count_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original all-negative-cutoff Poisson zero count event is precisely physical jumpfree on any ordered half-open interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t) :
    (∀ n : ℕ,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0) ↔
    (∀ u : ℝ≥0, s < u → u ≤ t →
      X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) := by
  constructor
  · exact avram_b125_original_all_zero_poisson_cutoff_counts_imply_true_jumpfree
      X ω s t hst
  · intro hNoJump n
    exact avram_b123_original_actual_jumpfree_implies_every_negative_count_zero
      X ω s t hst hNoJump n
