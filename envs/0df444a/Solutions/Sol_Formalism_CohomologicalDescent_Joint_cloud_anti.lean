-- Prove2me | solution 1 for Formalism.CohomologicalDescent.Joint.cloud_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:42:32.795802+00:00
-- url     : https://prove2.me/submissions/98289093-e776-41d9-aa3a-11cd5396161b

import Definitions.Def_Formalism_PieriBlockIdeals_StatementJ
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.Joint
open Formalism.RankGapBounds.ChebyshevFactorialBounds Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.Cor
namespace Formalism.CohomologicalDescent.Joint
theorem _root_.solution {ι : Type} {D : Data ι} (W : Weights D) (τ : ι) : StrictAnti (W.cloud τ) := by
  intro a b hab
  refine W.anti τ ?_
  have : (a : ℕ) < (b : ℕ) := hab
  exact this
end Formalism.CohomologicalDescent.Joint
