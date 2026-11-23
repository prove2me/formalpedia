-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx3.t_BlockFrame
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:42.062801+00:00
-- url     : https://prove2.me/submissions/dfeb1a6f-1864-482f-8837-4d111ea08547

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx3
namespace Formalism.FourierDecayAlt.P.Jx3
theorem _root_.solution : BlockFrame := by
  intro hL hE E _ _ _ hU g ν s hg
  obtain ⟨_, _, _, _, _, _, _, _, _, h10, h11, h12⟩ := hL E hU g ν s hg
  obtain ⟨a, b, c⟩ := hE E (S6.perLat E g ν s) (S6.rd E ^ (-ν)) h10 h11
  exact ⟨a, b, c.trans h12⟩
end Formalism.FourierDecayAlt.P.Jx3
