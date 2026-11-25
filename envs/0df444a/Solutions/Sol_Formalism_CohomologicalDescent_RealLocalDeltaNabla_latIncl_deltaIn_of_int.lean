-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.latIncl_deltaIn_of_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:22.480159+00:00
-- url     : https://prove2.me/submissions/76c9ec0a-e426-49cd-be68-f00658e22302

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_latIncl_iff_int_incl

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
variable (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ) (hl : l.Prime)
  (hlO : ¬ IsUnit (l : O)) (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i)
  (ν : ∀ i, Fin (n i) → ℕ) (e : ι → ℕ) (he : ∀ i, InclZ (r i) (n i) (hn i) (ν i) l (e i))
include hl hlO he
namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla
theorem _root_.solution (i : ι) : LatIncl (l : O) (deltaIn O (r i) (n i) (hn i) (ν i)) (e i) := (latIncl_iff_int_incl O l hl hlO (r i) (n i) (hn i) (ν i) (e i)).2 (he i)
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
