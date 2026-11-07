-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_turn17_compact_interval_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:24:26.284053+00:00
-- url     : https://prove2.me/submissions/38d1baed-15f7-4966-a8ca-a31fb30847a1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, 0 ≤ y → y ≤ 1 → w y ≤ M := by
  have hwIcc : ContinuousOn w (Icc (0 : ℝ) 1) :=
    hw_cont.mono (by
      intro y hy
      exact mem_Ici.mpr hy.1)
  have hc : IsCompact (w '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hwIcc
  obtain ⟨M, hM⟩ := hc.bddAbove
  refine ⟨max 0 M, le_max_left _ _, ?_⟩
  intro y hy0 hy1
  exact (hM (Set.mem_image_of_mem w (mem_Icc.mpr ⟨hy0, hy1⟩))).trans
    (le_max_right _ _)
