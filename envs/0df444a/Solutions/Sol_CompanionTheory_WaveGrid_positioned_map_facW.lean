-- Prove2me | solution 1 for CompanionTheory.WaveGrid.positioned_map_facW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:26:54.848487+00:00
-- url     : https://prove2.me/submissions/ae9574bd-ecd7-4c5a-a97b-d1f6bf478395

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
theorem _root_.solution (w : List C.Letter) (y : ℝ) :
    (D.positionted w).map (fun l => facW l (y : ℂ)) = w.map fun l => ((fac l y : ℝ) : ℂ) := by
  apply List.ext_getElem
  · simp [D.positionted]
  · intro n h1 h2
    simp only [D.positionted, List.getElem_map, List.getElem_ofFn, facW, fac]
    by_cases h : (w[n]'(by simpa using h2)).1
    · simp [h]
    · simp [h]
end CompanionTheory.WaveGrid
