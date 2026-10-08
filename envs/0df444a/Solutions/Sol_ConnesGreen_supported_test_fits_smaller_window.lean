-- Prove2me | solution 1 for ConnesGreen.supported_test_fits_smaller_window
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T21:01:11.358713+00:00
-- url     : https://prove2.me/submissions/42ec64e1-242b-4f54-bb03-7173f71d276f

import Definitions.Def_ConnesRZ_weil_defs
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ Set
noncomputable section

theorem solution (T : ℝ) (hT : 0 < T)
    (g : ℝ → ℂ) (hg : (IsTest g ∧ tsupport g ⊆ Ioo (-T) T)) :
    ∃ t : ℝ, 0 < t ∧ t < T ∧ (IsTest g ∧ tsupport g ⊆ Ioo (-t) t) := by
  by_cases hs : (tsupport g).Nonempty
  · obtain ⟨a, ha, hmax⟩ := hg.1.2.exists_isMaxOn hs continuous_abs.continuousOn
    have haT : |a| < T := abs_lt.mpr (hg.2 ha)
    let t := (|a| + T) / 2
    have ht : 0 < t := by dsimp [t]; linarith [abs_nonneg a]
    have htT : t < T := by dsimp [t]; linarith
    refine ⟨t, ht, htT, hg.1, ?_⟩
    intro x hx
    apply abs_lt.mp
    have hm : |x| ≤ |a| := hmax hx
    dsimp [t]
    linarith
  · refine ⟨T / 2, by linarith, by linarith, hg.1, ?_⟩
    exact fun x hx => False.elim (hs ⟨x, hx⟩)
