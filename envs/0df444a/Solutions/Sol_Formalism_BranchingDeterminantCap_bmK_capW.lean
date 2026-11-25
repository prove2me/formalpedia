-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_capW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:18:40.148801+00:00
-- url     : https://prove2.me/submissions/b5ba0d7e-d1a8-4b77-8428-904accb56ed2

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_isWH_of_comm
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_lastcomp_comm_bmEL
import Theorems.Thm_Formalism_BranchingDeterminantCap_capDet_commute_of
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_mem
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_mem_alt

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
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam : Fin n → ℕ) (d : ℕ) (u : ℤ)
    (G : BP R n) (hG : G ∈ bmW R n lam d) : bmCap R n u G ∈ bmW R n lam d := by
  rw [bmK_mem_alt] at hG ⊢
  refine ⟨bmK_mem lam u G hG.1, ?_⟩
  exact bm_isWH_of_comm (lastW n) d (bmCap R n u)
    (capDet_commute_of (bmEL R n) u _ (fun i j => bm_lastcomp_comm_bmEL R n d i j)) G hG.2
end Formalism.BranchingDeterminantCap
