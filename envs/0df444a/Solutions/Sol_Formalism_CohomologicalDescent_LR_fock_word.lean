-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.fock_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:24.317951+00:00
-- url     : https://prove2.me/submissions/3ff0191f-4ea0-417e-8773-24177ba85053

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrcFockZeroRight
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrc_applyWord_mem
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockQPos
import Theorems.Thm_Formalism_GradedWeylDivisibility_fock_space_highest_weight
import Theorems.Thm_Formalism_GradedWeylDivisibility_fock_space_word_adjoint


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
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (r : ℕ) (ν : Fin r → ℕ) (hν : Antitone ν) (F : MvPolynomial (Fin r × Fin r) ℚ)
    (hF : F ∈ dualWeyl ℚ r r ν) (w : List (Fin r × Fin r × ℕ)) :
    fockQ F (applyWord ℚ w (hw ℚ le_rfl ν)) =
      eval (idFrame ℚ r r) (applyWord ℚ (transposeWord w) F) * fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) := by
  rw [(fockQPos _ F _).1, fock_space_word_adjoint,
    fock_space_highest_weight r r le_rfl ν hν _ (lrc_applyWord_mem ℚ r r ν _ F hF)]
end Formalism.CohomologicalDescent.LR
