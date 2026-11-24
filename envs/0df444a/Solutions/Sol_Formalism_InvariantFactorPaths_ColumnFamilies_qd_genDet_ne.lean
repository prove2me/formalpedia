-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_genDet_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:37.054941+00:00
-- url     : https://prove2.me/submissions/7fe38fc4-d6ef-4dac-82e2-30f875329198

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) : (genMat ℚ n).det ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (fun ab : Fin n × Fin n => if ab.1 = ab.2 then (1 : ℚ) else 0)) h
  rw [RingHom.map_det] at this
  have h1 : (MvPolynomial.eval (fun ab : Fin n × Fin n => if ab.1 = ab.2 then (1 : ℚ) else 0)).mapMatrix (genMat ℚ n)
      = 1 := by
    ext a b; simp [genMat, Matrix.one_apply]
  rw [h1] at this
  simp at this
end Formalism.InvariantFactorPaths.ColumnFamilies
