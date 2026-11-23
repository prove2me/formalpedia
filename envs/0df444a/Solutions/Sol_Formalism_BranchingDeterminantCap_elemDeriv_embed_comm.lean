-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.elemDeriv_embed_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:06.52559+00:00
-- url     : https://prove2.me/submissions/1e593b98-e71e-4c8a-a560-a061fc5fa498

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_elemDeriv_X
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) (f : MvPolynomial (Fin n × Fin n) R) :
    bmE R n s t (emb R n f) = emb R n (ndE R n n s t f) := by
  induction f using MvPolynomial.induction_on
  next a => simp [emb, MvPolynomial.derivation_C]
  next p q hp hq => simp only [map_add, hp, hq]
  next p v hp =>
    have hX : bmE R n s t (emb R n (X v)) = emb R n (ndE R n n s t (X v)) := by
      simp only [emb, rename_X, elemDeriv_X, ndE, mkDerivation_X]
      by_cases h : v.2 = t <;> simp [h, Fin.castSucc_ne_last]
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, hX]
end Formalism.BranchingDeterminantCap
