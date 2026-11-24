-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_eval_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:20.879052+00:00
-- url     : https://prove2.me/submissions/9d07c754-3b12-4f19-b976-d8606c554f87

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnFactRowDivDiag
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnInterlacedLowerTri
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnEvalMap
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
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (Y : MvPolynomial (Fin n × Fin n) ℤ) :
    eval (idFrame ℚ n n) (map (Int.castRingHom ℚ) Y) = ((eval (idFrame ℤ n n) Y : ℤ) : ℚ) := by
  have h : (eval (idFrame ℚ n n)).comp (map (Int.castRingHom ℚ)) =
      (Int.castRingHom ℚ).comp (eval (idFrame ℤ n n)) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro v
      simp only [RingHom.coe_comp, Function.comp_apply, map_X, eval_X, idFrame]
      split_ifs <;> simp
  exact congrArg (fun φ => φ Y) h
end Formalism.InvariantFactorPaths.ColumnFamilies
