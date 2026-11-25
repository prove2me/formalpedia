-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:35:14.49792+00:00
-- url     : https://prove2.me/submissions/94eaf4a5-0ac7-46d1-a591-4ad786a70ae5

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_zcomp_comm_bmEL
import Theorems.Thm_Formalism_BranchingDeterminantCap_capDet_commute_of
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_kill
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_sep
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_list_kills
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_eig
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_comm
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_mem_alt
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
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam sg : Fin n → ℕ)
    (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) (G : BP R n)
    (hG : G ∈ bmW R n lam (∑ s, (lam s - sg s)))
    (h0 : zcomp R n (fun s => ((lam s - sg s : ℕ) : ℤ)) G = 0) : bmZop R n lam sg G = 0 :=
  bm_kill (zW n) omg (bmCap R n) (bmW R n lam (∑ s, (lam s - sg s))) (bmChi lam)
    (bmAdm lam (∑ s, (lam s - sg s))) (bmK_comm R n)
    (fun u β => capDet_commute_of (bmEL R n) u _ (bm_zcomp_comm_bmEL R n β)) (bmK_capW lam _)
    (fun G hG β h1 h2 => bm_eig lam _ G (bmK_mem_alt.1 hG).1 (bmK_mem_alt.1 hG).2 β h1 h2)
    (bm_sep lam _) (bmList lam sg) _ (bm_list_kills lam sg hI) G hG h0
end Formalism.BranchingDeterminantCap
