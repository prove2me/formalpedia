-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_lpMinor_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:53:03.643803+00:00
-- url     : https://prove2.me/submissions/2669434e-c8f0-4891-be4d-3fa4835b6e70

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
theorem _root_.solution (R : Type) [CommRing R] {r n : ℕ} (s : ℕ) (hs : s = 1) (hr : s ≤ r)
    (hn : s ≤ n) :
    lpMinor R s hr hn = X ((⟨0, by omega⟩ : Fin r), (⟨0, by omega⟩ : Fin n)) := by
  subst hs
  show Matrix.det (Matrix.of fun p q : Fin 1 =>
    (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)) = _
  rw [Matrix.det_fin_one]
  rfl
end Formalism.CohomologicalDescent.LA
