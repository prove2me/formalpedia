-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_spatial_exit_clip_identity_when_physical_path_below_upbarrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:31:13.14702+00:00
-- url     : https://prove2.me/submissions/e2576a5c-89f1-4b63-bacf-5cb1a480e7a1

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (σ : ℝ≥0) (a : ℝ)
    (hBelow : ∀ t : ℝ≥0, t ≤ σ → X.X t ω ≤ a) :
    (min (σ : ℝ≥0∞) (twoSidedExitUpTime X a ω)).toNNReal = σ := by
  classical
  have hUp : (σ : ℝ≥0∞) ≤ twoSidedExitUpTime X a ω := by
    change (σ : ℝ≥0∞) ≤
      (⨅ (s : ℝ≥0) (_ : a < X.X s ω), (s : ℝ≥0∞))
    refine le_iInf fun s => le_iInf fun hs => ?_
    have hlt : σ < s := by
      by_contra hn
      have hsσ : s ≤ σ := le_of_not_gt hn
      exact (not_lt_of_ge (hBelow s hsσ)) hs
    exact_mod_cast (le_of_lt hlt)
  rw [min_eq_left hUp]
  simp
