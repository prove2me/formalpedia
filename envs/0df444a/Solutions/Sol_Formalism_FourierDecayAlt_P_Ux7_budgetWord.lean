-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux7.budgetWord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:39:30.076042+00:00
-- url     : https://prove2.me/submissions/8598aaa7-e37b-4537-9498-22b651fa9854

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
theorem _root_.solution : BudgetWord := by
  intro N j r hj hjr
  refine ⟨Nat.mul_le_mul_left N hjr, ?_⟩
  have h1 : j ≤ r ^ 2 := hjr.trans (Nat.le_self_pow (by norm_num) r)
  have h2 : j ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hjr 2
  have a := Nat.mul_le_mul_left N h1
  have b := Nat.mul_le_mul_left N h2
  have c : j * (N * j) = N * j ^ 2 := by ring
  rw [c]
  nlinarith
end Formalism.FourierDecayAlt.P.Ux7
