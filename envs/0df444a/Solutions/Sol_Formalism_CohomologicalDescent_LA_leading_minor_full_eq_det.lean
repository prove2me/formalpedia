-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.leading_minor_full_eq_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:01:33.958795+00:00
-- url     : https://prove2.me/submissions/63bb6ce5-c70e-40b0-b471-c1bcaed4bbe9

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul

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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (R : Type) [CommRing R] {r : ℕ} (s : ℕ) (hs : s = r) (hr : s ≤ r)
    (hn : s ≤ r) : lpMinor R s hr hn = genericDet R r := by
  subst hs
  rfl
end Formalism.CohomologicalDescent.LA
