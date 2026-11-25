-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.budget_top_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:45:05.018728+00:00
-- url     : https://prove2.me/submissions/70a33ced-2eae-4716-8420-a67d73a0fabb

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetTopConvergence
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux7_budgetTop

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
theorem _root_.solution : Formalism.FourierDecayAlt.U.BudgetTop := by
  exact budgetTop
end Formalism.FourierDecayAlt.P
