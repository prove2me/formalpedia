-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.t_XIsLamOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:02.587627+00:00
-- url     : https://prove2.me/submissions/678c03ff-4ceb-417b-b33b-1cc4910aef1d

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped ComplexOrder
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution : XIsLamOne := by
  intro m i C ka N I A g B
  have h : 2 * i - 2 = 2 * (i - 1) + 1 - 1 := by omega
  constructor <;> simp only [Sz.xThreshold, Sz.lamThreshold, Sz.xHat, Sz.lamHat, h]
end Formalism.FourierDecayAlt.P.Jx7
