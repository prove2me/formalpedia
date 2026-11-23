-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmE_lead
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:31.34963+00:00
-- url     : https://prove2.me/submissions/45883eb3-db9a-4e68-9690-79bf253e621f

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_elemDeriv_lastMonomial_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_elemDeriv_embed_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) (b : Fin n → ℕ)
    (f : MvPolynomial (Fin n × Fin n) R) :
    bmE R n s t (zmon R n b * emb R n f) = zmon R n b * emb R n (ndE R n n s t f) := by
  rw [Derivation.leibniz, elemDeriv_lastMonomial_zero, smul_zero, add_zero, elemDeriv_embed_comm, smul_eq_mul]
end Formalism.BranchingDeterminantCap
