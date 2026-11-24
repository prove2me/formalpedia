-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldrow_rowAct_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:10.078591+00:00
-- url     : https://prove2.me/submissions/9f58a1d4-1333-4fa2-98ce-40170a22ca5f

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
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
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {k n : ℕ} :
    rowAct R (n := n) (1 : Matrix (Fin k) (Fin k) R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [rowAct, Matrix.one_apply, apply_ite C, ite_mul]
end Formalism.GradedWeylDivisibility
