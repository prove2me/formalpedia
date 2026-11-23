-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dualIdealEqLiftIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:54.175665+00:00
-- url     : https://prove2.me/submissions/40bb59d5-ead3-453d-9311-d0aa98bf095c

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x1
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S6.IdealsMatch := by
  intro E _ _ _ g r i s
  refine ⟨?_, ?_, ?_⟩
  · unfold dualIdl liftIdl nuBlock; congr 1; ring
  · unfold dualIdl nuBlock; congr 1; ring
  · unfold nuBlock; ring
end Formalism.FourierDecayAlt.P
