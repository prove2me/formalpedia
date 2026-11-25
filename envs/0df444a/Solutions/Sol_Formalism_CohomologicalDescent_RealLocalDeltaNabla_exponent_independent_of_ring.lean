-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.exponent_independent_of_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:42:25.283962+00:00
-- url     : https://prove2.me/submissions/c25eff44-da3a-4e68-af26-1e90acaf686a

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_exponent_eq_over_ring

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
theorem _root_.solution : ExZIndep := by
  intro O O' _ _ _ _ _ _ _ _ l hl hlO hlO' r n hn ν
  rw [← exponent_eq_over_ring O l hl hlO r n hn ν, ← exponent_eq_over_ring O' l hl hlO' r n hn ν]
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
