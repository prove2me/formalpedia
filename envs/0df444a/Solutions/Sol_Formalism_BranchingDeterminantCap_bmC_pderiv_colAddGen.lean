-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmC_pderiv_colAddGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:54.771181+00:00
-- url     : https://prove2.me/submissions/da2edd44-6cbc-43a1-9d2b-fbf9163e4b49

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmC_pderiv_colAddGen_X
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
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} {l j : Fin n} (hlj : l ≠ j)
    (g : MvPolynomial (Fin r × Fin n) R) :
    pderiv none (colAddGen R l j g) = colAddGen R l j (ndE R r n l j g) := by
  induction g using MvPolynomial.induction_on
  next a => simp [colAddGen, MvPolynomial.derivation_C]
  next p q hp hq => simp only [map_add, hp, hq]
  next p v hp => simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, bmC_pderiv_colAddGen_X hlj]
end Formalism.BranchingDeterminantCap
