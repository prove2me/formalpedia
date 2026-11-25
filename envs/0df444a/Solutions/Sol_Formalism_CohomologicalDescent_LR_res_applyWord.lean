-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.res_applyWord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:15:27.193856+00:00
-- url     : https://prove2.me/submissions/8e02c5b7-fd32-4bc6-94b2-ba1251c0009a

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrbPiSingleCast
import Theorems.Thm_Formalism_CohomologicalDescent_LR_res_rowDiv

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
theorem _root_.solution (ω : List (Fin q × Fin q × ℕ)) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) R) :
    res R p q (applyWord R (liftWord p ω) f) = applyWord R ω (res R p q f) := by
  induction ω with
  | nil => rfl
  | cons x ω ih =>
    change res R p q (rowDiv R _ _ _ (applyWord R (liftWord p ω) f)) = rowDiv R _ _ _ (applyWord R ω (res R p q f))
    rw [res_rowDiv, ih]
end Formalism.CohomologicalDescent.LR
