-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_nu_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:12.688271+00:00
-- url     : https://prove2.me/submissions/d5a17b5d-f278-4884-8563-9acbb7a3cc64

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) : Antitone (qd_nu mu) := by
  intro s t hst
  unfold qd_nu
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_le_sum fun c _ => ?_
  have : s.val ≤ t.val := hst
  unfold initW
  split_ifs <;> omega
end Formalism.InvariantFactorPaths.ColumnFamilies
