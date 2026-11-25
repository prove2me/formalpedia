-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.res_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:20:26.669797+00:00
-- url     : https://prove2.me/submissions/67dc8b1d-97cb-4082-8300-6e4ed02761e3

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrbPiSingleCast
import Theorems.Thm_Formalism_CohomologicalDescent_LR_res_rowDiv
import Theorems.Thm_Formalism_CohomologicalDescent_LR_res_eval_id
import Theorems.Thm_Formalism_CohomologicalDescent_LR_res_mem
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_blockWt_anti
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwLine
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwRaise
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_eval_idFrame_hw
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
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w) :
    res ℚ p q (hw ℚ le_rfl (LD.blockWt p q w lam2)) = hw ℚ le_rfl lam2 := by
  have hA := LD.ld_blockWt_anti p q w lam2 ha hb
  have hm := res_mem ℚ p q w lam2 _ (hwMem ℚ (p + q) (p + q) le_rfl _ hA)
  obtain ⟨c, hc⟩ := hwLine ℚ q q le_rfl lam2 ha _ hm (fun a b hab k hk => by
    rw [← res_rowDiv, hwRaise ℚ (p + q) (p + q) le_rfl _ (Fin.natAdd p a) (Fin.natAdd p b) k (by
      rw [Fin.lt_def] at hab ⊢
      simpa using hab) hk, map_zero])
  have h1 := res_eval_id ℚ p q (hw ℚ le_rfl (LD.blockWt p q w lam2))
  rw [lehw_eval_idFrame_hw, hc, smul_eval, lehw_eval_idFrame_hw, mul_one] at h1
  rw [hc, h1, one_smul]
end Formalism.CohomologicalDescent.LR
