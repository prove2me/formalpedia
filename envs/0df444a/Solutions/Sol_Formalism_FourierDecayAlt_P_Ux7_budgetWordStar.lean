-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux7.budgetWordStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:39:31.11429+00:00
-- url     : https://prove2.me/submissions/1b78c3d7-e4a8-4085-a32f-efb31811e7fe

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetTopConvergence

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux7
namespace Formalism.FourierDecayAlt.P.Ux7
theorem _root_.solution : BudgetWordStar := by
  intro N r n h
  have h1 : 3 * r ^ 2 ≤ n ^ 2 := by nlinarith
  have h2 := Nat.mul_le_mul_left N h1
  nlinarith [Nat.zero_le (n ^ 3)]
end Formalism.FourierDecayAlt.P.Ux7
