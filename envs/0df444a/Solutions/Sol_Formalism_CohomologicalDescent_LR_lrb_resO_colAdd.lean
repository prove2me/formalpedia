-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrb_resO_colAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:03:36.808841+00:00
-- url     : https://prove2.me/submissions/e06c6bd5-dee2-4f04-a6cd-4d3246511f6f

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrbPiSingleCast
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_var_ll
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_var_lr
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_var_rl
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_var_rr
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_res_X
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_cast_ne_nat
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_resO_some
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_resO_none
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
variable (R : Type*) [CommRing R] (p q : ℕ)
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (l j : Fin q) :
    (lrbResO R p q).comp (colAddGen R (Fin.natAdd p l) (Fin.natAdd p j)) = (colAddGen R l j).comp (res R p q) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  obtain ⟨x, s⟩ := v
  simp only [AlgHom.comp_apply, lrb_res_X]
  rw [colAddGen, aeval_X]
  refine Fin.addCases (fun a => ?_) (fun c => ?_) x <;> refine Fin.addCases (fun s' => ?_) (fun t => ?_) s
  · rw [if_neg (lrb_cast_ne_nat p q s' j), lrb_resO_some, lrb_var_ll]
    split_ifs <;> simp
  · simp only [Fin.natAdd_inj]
    split_ifs
    · rw [map_add, map_mul, lrb_resO_some, lrb_resO_some, lrb_var_lr, lrb_var_lr]
      simp
    · rw [lrb_resO_some, lrb_var_lr]
      simp
  · rw [if_neg (lrb_cast_ne_nat p q s' j), lrb_resO_some, lrb_var_rl]
    simp
  · simp only [Fin.natAdd_inj]
    rw [lrb_var_rr, colAddGen, aeval_X]
    simp only
    split_ifs
    · rw [map_add, map_mul, lrb_resO_some, lrb_resO_some, lrb_resO_none, lrb_var_rr, lrb_var_rr, rename_X, rename_X]
    · rw [lrb_resO_some, lrb_var_rr, rename_X]
end Formalism.CohomologicalDescent.LR
