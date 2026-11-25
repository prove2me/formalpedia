-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.padic_coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:11:51.826362+00:00
-- url     : https://prove2.me/submissions/16f92772-1ce5-4991-808f-a757211e23a0

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla

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
theorem _root_.solution : PadicCoeff := by
  intro p _
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  rw [PadicInt.isUnit_iff, PadicInt.norm_p, inv_eq_one]
  exact_mod_cast (Fact.out : p.Prime).one_lt.ne'
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
