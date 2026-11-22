-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_emb_WH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:11.268931+00:00
-- url     : https://prove2.me/submissions/205cfb25-aade-49f7-8004-532cdaec8fe3

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
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
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} {B : Type*} [AddCommMonoid B]
    (w : Fin (n + 1) × Fin n → B) (hw : ∀ (a : Fin n) (s : Fin n), w (a.castSucc, s) = 0)
    (f : MvPolynomial (Fin n × Fin n) R) : IsWeightedHomogeneous w (emb R n f) 0 := by
  induction f using MvPolynomial.induction_on
  next a =>
    rw [emb, rename_C]
    apply isWeightedHomogeneous_C
  next p q hp hq =>
    rw [map_add]
    exact hp.add hq
  next p v hp =>
    rw [map_mul]
    have hx : IsWeightedHomogeneous w (emb R n (X v)) 0 := by
      rw [emb, rename_X, ← hw v.1 v.2]
      apply isWeightedHomogeneous_X
    simpa using hp.mul hx
end Formalism.BranchingDeterminantCap
