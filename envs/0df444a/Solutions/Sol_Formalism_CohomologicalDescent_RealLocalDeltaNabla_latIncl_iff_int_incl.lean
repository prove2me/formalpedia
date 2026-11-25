-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.latIncl_iff_int_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:57:44.024889+00:00
-- url     : https://prove2.me/submissions/9903040b-69f1-47f2-90a7-ae0ec6af5d7c

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_lattice_incl_iff_ring
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
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ)
    (hl : l.Prime) (hlO : ¬ IsUnit (l : O)) (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (e : ℕ) :
    LatIncl (l : O) (deltaIn O r n hn ν) e ↔ InclZ r n hn ν l e := (latIncl_deltaIn_iff_dual_weyl O r n hn ν (l : O) e).trans (lattice_incl_iff_ring O l hl hlO r n hn ν e).symm
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
