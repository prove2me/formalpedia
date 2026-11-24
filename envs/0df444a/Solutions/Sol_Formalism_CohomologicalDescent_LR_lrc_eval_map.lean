-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrc_eval_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:38:09.348865+00:00
-- url     : https://prove2.me/submissions/007e5466-5f3d-404a-87d3-9d9ff13c0696

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrcFockZeroRight
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
theorem _root_.solution (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    eval (idFrame ℚ r n) (map (Int.castRingHom ℚ) P) = ((eval (idFrame ℤ r n) P : ℤ) : ℚ) := by
  have h : (eval (idFrame ℚ r n)).comp (map (Int.castRingHom ℚ)) =
      (Int.castRingHom ℚ).comp (eval (idFrame ℤ r n)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro v
      simp only [RingHom.comp_apply, map_X, eval_X, idFrame]
      split_ifs <;> simp
  exact congrArg (fun F => F P) h
end Formalism.CohomologicalDescent.LR
