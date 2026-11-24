-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrc_applyWord_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:38:07.76634+00:00
-- url     : https://prove2.me/submissions/ec5ca061-9225-4c37-ba2b-5839b1d8f86d

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrcFockZeroRight
import Theorems.Thm_Formalism_GradedWeylDivisibility_applyWord_cons
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivStable


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
theorem _root_.solution (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) : applyWord R w f ∈ dualWeyl R r n ν := by
  induction w with
  | nil => exact hf
  | cons x w ih =>
    rw [applyWord_cons]
    exact rowDivStable R r n ν _ _ _ _ ih
end Formalism.CohomologicalDescent.LR
