-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.raising_exponent_interval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:23:47.310192+00:00
-- url     : https://prove2.me/submissions/473c99ac-307f-4143-a5fe-fc3285008be1

import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_sum_maxVal_le_card_mul_log
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_card_posPairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial CategoryTheory TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.SL2BinomialLattices
open Formalism.GradedWeylDivisibility Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.LA
universe u v u' v'
namespace Formalism.CohomologicalDescent.SL2BinomialLattices
theorem _root_.solution : EExpInterval := by
  intro l N h U lo hl hU hr
  have h1 := sum_maxVal_le_card_mul_log U l h hl.pos (posPairs N) (by
    intro p _
    have h2 := hr p.1
    have h3 := hr p.2
    omega)
  rw [card_posPairs] at h1
  exact h1
end Formalism.CohomologicalDescent.SL2BinomialLattices
