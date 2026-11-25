-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.budget_word_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:37:30.448677+00:00
-- url     : https://prove2.me/submissions/f9cf4668-b353-4775-8cfc-9158f58264b4

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetTopConvergence
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux7_budgetWordStar

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
theorem _root_.solution : Formalism.FourierDecayAlt.U.BudgetWordStar := by
  exact budgetWordStar
end Formalism.FourierDecayAlt.P
