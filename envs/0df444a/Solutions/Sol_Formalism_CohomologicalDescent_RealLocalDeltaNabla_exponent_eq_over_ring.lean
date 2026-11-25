-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.exponent_eq_over_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:57:49.115007+00:00
-- url     : https://prove2.me/submissions/ea160535-eb71-4a60-a113-6621c9fc1d5c

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_lattice_incl_iff_ring

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
theorem _root_.solution : ExZEqO := by
  intro O _ _ _ _ l hl hlO r n hn ν
  unfold exZ
  congr 1
  ext e
  exact lattice_incl_iff_ring O l hl hlO r n hn ν e
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
