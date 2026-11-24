-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.GlRel.commF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:49:48.051289+00:00
-- url     : https://prove2.me/submissions/bc6146b7-32cc-48c2-b173-56b1dd87fb14

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
namespace Formalism.InvariantFactorPaths.PW
namespace GlRel
theorem _root_.solution {E : ι → ι → Module.End K W} (h : GlRel E) {z i j : ι} (hi : i ≠ z) (hj : j ≠ z) :
    Commute (E z i) (E z j) := by
  have := h z i z j
  simp only [hi, hj, if_false, sub_self] at this
  exact sub_eq_zero.mp this
end GlRel
end Formalism.InvariantFactorPaths.PW
