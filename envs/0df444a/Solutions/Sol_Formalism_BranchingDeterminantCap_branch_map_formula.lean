-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.branch_map_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:19:19.563159+00:00
-- url     : https://prove2.me/submissions/fc997509-5d65-41ba-8127-8027aaa262c6

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_weight_lastW
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_rowAct_comm_bmEL
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmE_comm_apply
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_IL_of
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_rowAct
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_xi
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_mem_alt
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_Zc
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_ZW
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_liftW
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_xi
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_rel_ex
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_io

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
theorem _root_.solution : BranchMap := by
  intro R _ _ _ n lam sg hI
  obtain ⟨io, hio⟩ := bmK_io (R := R) lam sg hI
  have hIL := bm_IL_of lam sg hI
  refine ⟨io, fun f => ?_, fun g f f' hf => ?_, fun h hh => ?_, fun f m hm => ?_⟩
  · obtain ⟨G, hG⟩ := bmK_rel_ex lam sg hIL f
    rw [hio f G hG]
    exact (bmK_mem_alt.mp (bmK_ZW lam sg _ G (bmK_liftW hG))).1
  · obtain ⟨G, hG⟩ := bmK_rel_ex lam sg hIL f
    have hG' : bmRel R n lam sg f' (rowAct R (extM R g) G) := by
      unfold bmRel
      rw [hf]
      exact bmLift_rowAct g hG
    rw [hio f' _ hG', hio f G hG]
    exact (bmE_comm_apply (bmK_Zc R n lam sg _ (fun i j => bm_rowAct_comm_bmEL R n g i j)) G).symm
  · have hx : bmRel R n lam sg h (xiB R lam sg) := by
      unfold bmRel
      rw [hh]
      exact bmLift_xi lam sg hIL
    rw [hio h _ hx]
    exact bmK_xi lam sg hI
  · obtain ⟨G, hG⟩ := bmK_rel_ex lam sg hIL f
    rw [hio f G hG] at hm
    have hW := bmK_mem_alt.mp (bmK_ZW lam sg _ G (bmK_liftW hG))
    have := hW.2 (mem_support_iff.mp hm)
    rw [bm_weight_lastW] at this
    exact this
end Formalism.BranchingDeterminantCap
