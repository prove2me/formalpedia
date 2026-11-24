-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_lpMinor_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:51:33.078134+00:00
-- url     : https://prove2.me/submissions/bb00dac1-7599-4a27-9c4b-2ad6e26e8d75

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan

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
theorem _root_.solution (R : Type) [CommRing R] (s : ℕ) (hs : s = 2) (hr : s ≤ 2) (hn : s ≤ 2) :
    lpMinor R s hr hn = la_det R := by
  subst hs
  show Matrix.det (Matrix.of fun p q : Fin 2 =>
    (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin 2 × Fin 2) R)) = _
  rw [Matrix.det_fin_two]
  rfl
end Formalism.CohomologicalDescent.LA
