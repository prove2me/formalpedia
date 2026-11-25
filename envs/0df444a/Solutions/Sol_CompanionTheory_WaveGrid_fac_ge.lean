-- Prove2me | solution 1 for CompanionTheory.WaveGrid.fac_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:25:02.262981+00:00
-- url     : https://prove2.me/submissions/493e9158-988b-4936-bdbe-95ddbef7c00c

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_QwBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt
namespace CompanionTheory.WaveGrid
theorem _root_.solution (l : C.Letter) (y : ℝ) (h : 4 ≤ |y - l.2|) : 3 / 4 ≤ fac l y := by
  unfold fac
  split_ifs
  · rcases le_abs'.1 h with h' | h'
    · have hneg : y - l.2 < 0 := by linarith
      rw [le_div_iff_of_neg hneg]
      linarith
    · have hpos : 0 < y - l.2 := by linarith
      rw [le_div_iff₀ hpos]
      linarith
  · rcases le_abs'.1 h with h' | h'
    · have hpos : 0 < l.2 - y - 1 := by linarith
      rw [le_div_iff₀ hpos]
      linarith
    · have hneg : l.2 - y - 1 < 0 := by linarith
      rw [le_div_iff_of_neg hneg]
      linarith
end CompanionTheory.WaveGrid
