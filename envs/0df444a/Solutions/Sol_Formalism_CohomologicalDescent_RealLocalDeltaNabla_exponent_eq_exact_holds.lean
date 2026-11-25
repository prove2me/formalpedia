-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.exponent_eq_exact_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:23.59629+00:00
-- url     : https://prove2.me/submissions/8d8621c3-1cf9-42ad-8b6f-4df505a162e0

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_exponent_eq_over_ring
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_latIncl_deltaIn_iff_dual_weyl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.RealLocalDeltaNabla
open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices
namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla
theorem _root_.solution : ExZEqExact := by
  intro O _ _ _ _ l hl hlO r n hn ν
  rw [exponent_eq_over_ring O l hl hlO r n hn ν]
  unfold Formalism.CohomologicalDescent.exactExp
  congr 1
  ext e
  exact (latIncl_deltaIn_iff_dual_weyl O r n hn ν (l : O) e).symm
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
