-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.lattice_incl_iff_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:32.657876+00:00
-- url     : https://prove2.me/submissions/fdd5e1d4-fdf3-47a8-bfa4-e414ae78506f

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_int_localisation_in_ring
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_lattice_incl_iff_over_int

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
theorem _root_.solution : InclZIffO := by
  intro O _ _ _ _ l hl hlO r n hn ν e
  obtain ⟨R, _, _, _, _, _, hloc, hinj, hu, hd⟩ := int_localisation_in_ring O l hl hlO
  exact lattice_incl_iff_over_int R O hinj l hl hu hd r n hn ν e
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
