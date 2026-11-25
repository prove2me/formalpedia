-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_ZW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:27:21.784364+00:00
-- url     : https://prove2.me/submissions/3a3063ae-2721-4076-8517-bbd0fb77f1a0

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_list_mem
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_capW

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
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam sg : Fin n → ℕ) (d : ℕ)
    (G : BP R n) (hG : G ∈ bmW R n lam d) : bmZop R n lam sg G ∈ bmW R n lam d := by
  exact bmK_list_mem (bmCap R n) (bmW R n lam d) (fun u G hG => bmK_capW lam d u G hG) (bmList lam sg) G hG
end Formalism.BranchingDeterminantCap
