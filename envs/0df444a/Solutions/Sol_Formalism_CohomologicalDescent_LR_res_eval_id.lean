-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.res_eval_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:03:37.842802+00:00
-- url     : https://prove2.me/submissions/d7c131af-8a10-41c8-b6e4-5c5ee970050a

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
theorem _root_.solution (f : MvPolynomial (Fin (p + q) × Fin (p + q)) R) :
    eval (idFrame R q q) (res R p q f) = eval (idFrame R (p + q) (p + q)) f := by
  have h : ((aeval (idFrame R q q) : MvPolynomial (Fin q × Fin q) R →ₐ[R] R).comp (res R p q)) =
      (aeval (idFrame R (p + q) (p + q)) : MvPolynomial (Fin (p + q) × Fin (p + q)) R →ₐ[R] R) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    obtain ⟨x, s⟩ := v
    simp only [AlgHom.comp_apply, lrb_res_X, aeval_X]
    refine Fin.addCases (fun a => ?_) (fun c => ?_) x <;> refine Fin.addCases (fun s' => ?_) (fun t => ?_) s
    · rw [lrb_var_ll]
      simp only [idFrame, Fin.val_castAdd, Fin.val_inj]
      split_ifs <;> simp
    · rw [lrb_var_lr]
      have := a.isLt
      simp only [idFrame, Fin.val_castAdd, Fin.val_natAdd, map_zero]
      rw [if_neg (by omega)]
    · rw [lrb_var_rl]
      have := s'.isLt
      simp only [idFrame, Fin.val_castAdd, Fin.val_natAdd, map_zero]
      rw [if_neg (by omega)]
    · rw [lrb_var_rr, aeval_X]
      simp only [idFrame, Fin.val_natAdd, add_right_inj]
  have h2 := congrArg (fun φ => φ f) h
  simpa [AlgHom.comp_apply, aeval_eq_eval] using h2
end Formalism.CohomologicalDescent.LR
