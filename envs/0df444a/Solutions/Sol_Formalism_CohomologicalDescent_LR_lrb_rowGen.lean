-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrb_rowGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:14:25.006511+00:00
-- url     : https://prove2.me/submissions/e7ed0232-b913-46d4-bd74-e27fecd0b789

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
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_mapC
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_mapX
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
theorem _root_.solution (b b' : Fin q) :
    (Polynomial.mapAlgHom (res R p q)).comp (rowGen R (Fin.natAdd p b) (Fin.natAdd p b')) =
      (rowGen R b b').comp (res R p q) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  obtain ⟨x, s⟩ := v
  simp only [AlgHom.comp_apply, lrb_res_X]
  rw [rowGen, aeval_X]
  refine Fin.addCases (fun a => ?_) (fun c => ?_) x
  · rw [if_neg (lrb_cast_ne_nat p q a b'), add_zero, lrb_mapC]
    refine Fin.addCases (fun s' => ?_) (fun t => ?_) s
    · rw [lrb_var_ll]
      split_ifs <;> simp
    · rw [lrb_var_lr]
      simp
  · refine Fin.addCases (fun s' => ?_) (fun t => ?_) s
    · rw [map_add, lrb_mapC, lrb_var_rl]
      split_ifs
      · rw [map_mul, lrb_mapC, lrb_var_rl]
        simp
      · simp
    · rw [map_add, lrb_mapC, lrb_var_rr, rowGen, aeval_X]
      simp only [Fin.natAdd_inj]
      split_ifs
      · rw [map_mul, lrb_mapC, lrb_mapX, lrb_var_rr]
      · simp
end Formalism.CohomologicalDescent.LR
