-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.branch_norm_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:12:44.894929+00:00
-- url     : https://prove2.me/submissions/405d8388-7ef5-456a-bf20-e3bc5a88e8ed

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Theorems.Thm_Formalism_BranchingDeterminantCap_bs_fock_smul_left
import Theorems.Thm_Formalism_BranchingDeterminantCap_bs_fock_smul_right
import Theorems.Thm_Formalism_BranchingDeterminantCap_branch_scale_formula
import Theorems.Thm_Formalism_BranchingDeterminantCap_branch_isometry
import Theorems.Thm_Formalism_BranchingDeterminantCap_bs_antitone
import Theorems.Thm_Formalism_BranchingDeterminantCap_bs_zScale_hw
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwMem
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
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : BranchNormT := by
  intro n lam sg t hint io heq hhw hdeg
  refine ⟨bs_zScale_hw n lam t, fun f => ?_⟩
  have hsg := bs_antitone lam sg hint
  let h : ↥(dualWeyl ℂ n n sg) := ⟨hw ℂ le_rfl sg, hwMem ℂ n n le_rfl sg hsg⟩
  have e1 := (branch_scale_formula n n _ t (io f) (hdeg f)).2
  have e2 := branch_isometry n sg hsg io heq f h rfl
  have e3 := hhw h rfl
  rw [e3, bs_fock_smul_left, bs_fock_smul_right] at e2
  have hstar : star (((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : ℂ)) =
      ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : ℂ) := by simp
  rw [hstar] at e2
  rw [e1, mul_assoc, e2]
  ring
end Formalism.BranchingDeterminantCap
