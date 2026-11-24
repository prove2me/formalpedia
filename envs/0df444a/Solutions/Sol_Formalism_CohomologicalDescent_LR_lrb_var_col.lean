-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrb_var_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:13:30.493073+00:00
-- url     : https://prove2.me/submissions/2a8cffac-a354-44fd-b176-c3b2f86c320d

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
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_pi_single_cast
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_pi_single_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable (R : Type*) [CommRing R] (p q : ℕ)
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (v : Fin (p + q) × Fin (p + q)) :
    IsWeightedHomogeneous (colW q q) (resVar R p q v) (lrbPi p q (colW (p + q) (p + q) v)) := by
  obtain ⟨x, s⟩ := v
  refine Fin.addCases (fun a => ?_) (fun c => ?_) x <;> refine Fin.addCases (fun s' => ?_) (fun t => ?_) s
  · rw [lrb_var_ll]
    change IsWeightedHomogeneous _ _ (lrbPi p q (Pi.single (Fin.castAdd q s') 1))
    rw [lrb_pi_single_cast]
    split_ifs
    · exact isWeightedHomogeneous_one _ _
    · exact isWeightedHomogeneous_zero _ _ _
  · rw [lrb_var_lr]
    exact isWeightedHomogeneous_zero _ _ _
  · rw [lrb_var_rl]
    exact isWeightedHomogeneous_zero _ _ _
  · rw [lrb_var_rr]
    change IsWeightedHomogeneous _ _ (lrbPi p q (Pi.single (Fin.natAdd p t) 1))
    rw [lrb_pi_single_nat]
    exact isWeightedHomogeneous_X _ _ _
end Formalism.CohomologicalDescent.LR
