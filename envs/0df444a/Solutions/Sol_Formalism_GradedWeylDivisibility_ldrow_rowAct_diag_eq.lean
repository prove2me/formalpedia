-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldrow_rowAct_diag_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:07.303111+00:00
-- url     : https://prove2.me/submissions/cf9f8ca7-7cf2-4e98-82e6-d6dd13b50e1c

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
theorem _root_.solution {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R) :
    rowAct R (n := n) (Matrix.diagonal t) = aeval fun v : Fin k × Fin n => C (t v.1) * X v := by
  unfold rowAct
  congr 1
  funext v
  simp [Matrix.diagonal_apply, apply_ite C, ite_mul]
end Formalism.GradedWeylDivisibility
