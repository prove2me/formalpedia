-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.derivative_bound_composition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:02:03.461481+00:00
-- url     : https://prove2.me/submissions/82d221bf-c9b7-40de-ae60-a7aeae3be76c

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetTopConvergence
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux7_derivBoundComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism.FourierDecayAlt.P.Ux7
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.U.DerivBoundComp := by
  exact derivBoundComp
end Formalism.FourierDecayAlt.P
