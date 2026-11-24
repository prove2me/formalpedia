-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_D_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:21.060697+00:00
-- url     : https://prove2.me/submissions/07b6bcdd-b5bc-4569-ac1e-8328d61d38fd

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
theorem _root_.solution (n : ℕ) (a b : Fin n) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    qn_D n a b f = ∑ l : Fin n, X (l, a) * pderiv (l, b) f := by
  unfold qn_D
  have h := map_sum (Derivation.coeFnAddMonoidHom (R := ℚ) (A := MvPolynomial (Fin n × Fin n) ℚ)
    (M := MvPolynomial (Fin n × Fin n) ℚ)) (fun l : Fin n => (X (l, a) : MvPolynomial (Fin n × Fin n) ℚ) • pderiv (l, b))
    Finset.univ
  have h2 := congrFun h f
  simp only [Finset.sum_apply] at h2
  exact h2.trans (Finset.sum_congr rfl fun l _ => by simp [Derivation.coeFnAddMonoidHom, smul_eq_mul])
end Formalism.InvariantFactorPaths.ColumnFamilies
