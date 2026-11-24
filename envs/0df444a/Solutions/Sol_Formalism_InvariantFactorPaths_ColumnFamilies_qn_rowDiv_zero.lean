-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_rowDiv_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:27.216252+00:00
-- url     : https://prove2.me/submissions/13fd4577-930b-482b-b2f7-9ad145aa52e6

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnFactRowDivDiag
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
theorem _root_.solution (n : ℕ) (a b : Fin n) (F : MvPolynomial (Fin n × Fin n) ℚ) :
    rowDiv ℚ a b 0 F = F := by
  unfold rowDiv
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have h : (Polynomial.evalRingHom (0 : MvPolynomial (Fin n × Fin n) ℚ)).comp
      (rowGen ℚ (r := n) (n := n) a b).toRingHom =
      RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowGen]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rowGen, aeval_X,
        Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C, RingHom.id_apply]
      split_ifs <;> simp
  have h2 := RingHom.congr_fun h F
  simpa using h2
end Formalism.InvariantFactorPaths.ColumnFamilies
