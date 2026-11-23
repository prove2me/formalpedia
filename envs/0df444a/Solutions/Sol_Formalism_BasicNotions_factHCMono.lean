-- Prove2me | solution 1 for Formalism.BasicNotions.factHCMono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:33.888801+00:00
-- url     : https://prove2.me/submissions/2619a995-26e4-4a6c-9345-440267cac3e3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_EvalFrameOrd
import Definitions.Def_Formalism_LocalRingCardinality_Params

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BasicNotions
namespace Formalism.BasicNotions
theorem _root_.solution : FactHCMono := by
  intro R P
  have ht : (0 : ℚ) ≤ R.t := by positivity
  refine ⟨fun i => ⟨P.u_gt_v i, P.v_gt_u i⟩, P.u_last_gt, fun j => ?_, fun j h => ?_⟩
  · have := P.gap_be j
    linarith
  · have := P.gap_eb j h
    linarith
end Formalism.BasicNotions
