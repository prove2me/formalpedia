-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_laplace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:46.02955+00:00
-- url     : https://prove2.me/submissions/2c8c717c-06cc-46a6-b5ad-223e4ef25bac

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_emb_minor
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) {s : ℕ} (I : Fin s → Fin n) (hs : s + 1 ≤ n) :
    initMinor R (fun p : Fin (s + 1) => if h : p.val < s then (I ⟨p.val, h⟩).castSucc else Fin.last n) hs =
      ∑ j : Fin (s + 1), (-1 : BP R n) ^ (s + (j : ℕ)) * X (Fin.last n, Fin.castLE hs j) *
        emb R n (Matrix.of fun p q : Fin s =>
          (X (I p, Fin.castLE hs (j.succAbove q)) : MvPolynomial (Fin n × Fin n) R)).det := by
  unfold initMinor
  rw [Matrix.det_succ_row _ (Fin.last s)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bmF_emb_minor]
  congr 1
  · congr 1
    simp
  · congr 1
    ext p q
    simp [Matrix.submatrix_apply, Fin.succAbove_last]
end Formalism.BranchingDeterminantCap
