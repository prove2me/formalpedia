-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.GlRel.commE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:33.321169+00:00
-- url     : https://prove2.me/submissions/ea5f00cc-1e1c-4cb6-889f-f5aca776c209

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
    Commute (E i z) (E j z) := by
  have := h i z j z
  simp only [Ne.symm hi, Ne.symm hj, if_false, sub_self] at this
  exact sub_eq_zero.mp this
end GlRel
end Formalism.InvariantFactorPaths.PW
