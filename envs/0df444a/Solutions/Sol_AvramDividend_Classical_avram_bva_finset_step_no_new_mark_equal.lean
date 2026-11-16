-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_finset_step_no_new_mark_equal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:46:08.041044+00:00
-- url     : https://prove2.me/submissions/8e5f70c3-8eed-4d0e-a1dc-347a45b717df

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical Set AvramDividend.Classical
open scoped NNReal BigOperators
noncomputable section

theorem solution
    (S : Finset ℝ≥0) (w : ℝ≥0 → ℝ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hNo : ∀ u ∈ S, ¬ (s < u ∧ u ≤ t)) :
    Finset.sum S (fun u => if u ≤ s then w u else 0) =
    Finset.sum S (fun u => if u ≤ t then w u else 0) := by
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hus : u ≤ s
  · have hut : u ≤ t := le_trans hus hst
    simp [hus, hut]
  · have hut : ¬ u ≤ t := by
      intro hut
      exact hNo u hu ⟨lt_of_not_ge hus, hut⟩
    simp [hus, hut]
