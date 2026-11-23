-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmLift_minor0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:37.990504+00:00
-- url     : https://prove2.me/submissions/72c72e8a-e6bc-465d-86d2-7f10a03986d2

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_low_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_emb_WH
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_lastW_castSucc
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_emb_minor
import Theorems.Thm_Formalism_GradedWeylDivisibility_initMinor_mem
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) {s : ℕ} (I : Fin s → Fin n) (hs : s ≤ n) :
    bmLift R n (initW n s) 0 (initMinor R I hs) (initMinor R (fun p => (I p).castSucc) hs) := by
  have he : initMinor R (fun p => (I p).castSucc) hs = emb R n (initMinor R I hs) := by
    unfold initMinor
    rw [bmF_emb_minor]
  refine ⟨initMinor_mem _ hs, ?_, ?_⟩
  · rw [he]
    simpa using bmF_emb_WH (lastW n) bmF_lastW_castSucc (initMinor R I hs)
  · have : initMinor R (fun p => (I p).castSucc) hs - zmon R n 0 * emb R n (initMinor R I hs) = 0 := by
      rw [he]; simp [zmon]
    rw [this]
    exact bmF_low_zero _
end Formalism.BranchingDeterminantCap
