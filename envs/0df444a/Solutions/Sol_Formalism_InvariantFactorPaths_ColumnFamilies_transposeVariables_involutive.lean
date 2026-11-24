-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.transposeVariables_involutive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:23.047891+00:00
-- url     : https://prove2.me/submissions/0e5aa2e8-99bb-45f3-b3f5-350bc1ca932d

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (f : MvPolynomial (Fin n × Fin n) R) :
    transposeVariables R n (transposeVariables R n f) = f := by
  simp only [transposeVariables, AlgHom.coe_comp, Function.comp_apply, MvPolynomial.rename_rename]
  have h : (Prod.swap ∘ Prod.swap : Fin n × Fin n → Fin n × Fin n) = id := by
    funext x
    simp
  rw [h]
  exact MvPolynomial.rename_id_apply f
end Formalism.InvariantFactorPaths.ColumnFamilies
