-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.lattice_incl_iff_over_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:44:28.504613+00:00
-- url     : https://prove2.me/submissions/bb31d7aa-033e-4e31-8578-5f7167f8a4dd

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_local_faithfully_flat_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LA_incl_z_iff_incl_r
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_lattice_baseChange_alt


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
theorem _root_.solution : InclZIffOver := by
  intro R O _ _ _ _ _ _ _ _ _ hinj l hl h1 h2 r n hn ν e
  have := local_faithfully_flat_holds R O hinj
  have h := lattice_baseChange_alt R O r n hn ν (l : R) e
  rw [map_natCast] at h
  rw [← h]
  exact incl_z_iff_incl_r R l hl h1 h2 r n hn ν e
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
