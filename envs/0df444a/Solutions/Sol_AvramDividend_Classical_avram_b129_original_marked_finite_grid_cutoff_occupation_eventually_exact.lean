-- Prove2me | solution 1 for AvramDividend.Classical.avram_b129_original_marked_finite_grid_cutoff_occupation_eventually_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:26:08.785206+00:00
-- url     : https://prove2.me/submissions/3bb32aa5-f388-4afa-9e68-e1c35db09cc7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b118_original_finite_physically_marked_cells_one_cutoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True original finite stopped-grid marked occupancy is exactly attained by one finite negative cutoff and all later cutoffs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (hMarked : ∀ i ∈ S, ∃ u : ℝ≥0,
      s i < u ∧ u ≤ t i ∧
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (J : ℕ → Finset ℕ)
    (hJsub : ∀ n, J n ⊆ S)
    (hJmono : ∀ n m, n ≤ m → J n ⊆ J m)
    (hJcapture : ∀ (n : ℕ) (i : ℕ), i ∈ S →
      (∃ u : ℝ≥0, s i < u ∧ u ≤ t i ∧
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1))) → i ∈ J n) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → J n = S := by
  obtain ⟨N, hN⟩ :=
    avram_b118_original_finite_physically_marked_cells_one_cutoff
      X ω S s t hMarked
  refine ⟨N, ?_⟩
  intro n hn
  apply Finset.Subset.antisymm (hJsub n)
  intro i hi
  exact hJmono N n hn (hJcapture N i hi (hN i hi))
