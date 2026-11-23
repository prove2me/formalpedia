-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_rowAct_comm_bmEL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:18.817799+00:00
-- url     : https://prove2.me/submissions/e48e8c2f-601a-435b-b10b-435b0fae350e

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_rowAction_ext_elemDeriv_X
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
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (g : Matrix (Fin n) (Fin n) R) (s t : Fin n) :
    Commute ((rowAct R (extM R g)).toLinearMap : Module.End R (BP R n)) (bmEL R n s t) := by
  refine LinearMap.ext fun F => ?_
  show rowAct R (extM R g) (bmE R n s t F) = bmE R n s t (rowAct R (extM R g) F)
  induction F using MvPolynomial.induction_on
  next a => simp [rowAct, MvPolynomial.derivation_C]
  next p q hp hq => simp only [map_add, hp, hq]
  next p v hp => simp only [Derivation.leibniz, map_mul, map_add, smul_eq_mul, hp, rowAction_ext_elemDeriv_X]
end Formalism.BranchingDeterminantCap
