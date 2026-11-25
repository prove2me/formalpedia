-- Prove2me | solution 1 for CompanionTheory.WaveGrid.ofReal_prod_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:25:03.988239+00:00
-- url     : https://prove2.me/submissions/7aa5e33f-af22-4f7f-a2e1-34199b5a0974

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
theorem _root_.solution (w : List C.Letter) (f : C.Letter → ℝ) :
    (((w.map f).prod : ℝ) : ℂ) = (w.map fun l => ((f l : ℝ) : ℂ)).prod := by
  induction w with
  | nil => simp
  | cons l w ih => simp [ih]
end CompanionTheory.WaveGrid
