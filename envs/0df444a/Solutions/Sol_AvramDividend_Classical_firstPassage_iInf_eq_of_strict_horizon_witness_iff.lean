-- Prove2me | solution 1 for AvramDividend.Classical.firstPassage_iInf_eq_of_strict_horizon_witness_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:36:43.965516+00:00
-- url     : https://prove2.me/submissions/ed023964-de87-420b-a9e0-96c6a8c73474

import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.CompleteLattice.Defs

open scoped ENNReal
theorem solution
    {ι κ : Sort*} (f : ι → ℝ≥0∞) (g : κ → ℝ≥0∞)
    (h : ∀ T : ℝ≥0∞, (∃ i, f i < T) ↔ (∃ j, g j < T)) :
    (⨅ i, f i) = (⨅ j, g j) := by
  apply le_antisymm
  · refine le_of_forall_gt fun c hc => ?_
    obtain ⟨j, hj⟩ := iInf_lt_iff.1 hc
    obtain ⟨i, hi⟩ := (h c).2 ⟨j, hj⟩
    exact iInf_lt_iff.2 ⟨i, hi⟩
  · refine le_of_forall_gt fun c hc => ?_
    obtain ⟨i, hi⟩ := iInf_lt_iff.1 hc
    obtain ⟨j, hj⟩ := (h c).1 ⟨i, hi⟩
    exact iInf_lt_iff.2 ⟨j, hj⟩
