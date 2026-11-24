-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.finite_over_padic_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:23.973454+00:00
-- url     : https://prove2.me/submissions/0330ab6c-7cd3-4c30-a28e-b57daf21fe2e

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_coefficient_over_holds
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


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
theorem _root_.solution : FiniteOverPadic := by
  intro p _ O _ _ _ hinj
  have hloc : IsLocalHom (algebraMap ℤ_[p] O) :=
    (algebraMap_isIntegral_iff.mpr inferInstance).isLocalHom hinj
  obtain ⟨h1, h2⟩ := coefficient_over_holds ℤ_[p] O hinj p PadicInt.p_nonunit
  exact ⟨hloc, h1, h2⟩
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
