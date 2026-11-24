-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.raising_split_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:13:16.816101+00:00
-- url     : https://prove2.me/submissions/5edf58bf-b6d5-4b85-96cf-50473bfd07f1

import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_sum_posPairs_split

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
theorem _root_.solution : ESplit3 := by
  intro N k l U
  exact sum_posPairs_split k _
end Formalism.CohomologicalDescent.SL2BinomialLattices
