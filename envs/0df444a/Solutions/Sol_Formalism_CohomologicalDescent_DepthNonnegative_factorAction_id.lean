-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.factorAction_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:13:27.406013+00:00
-- url     : https://prove2.me/submissions/ac1b580a-3328-4fee-9ea0-298cca4c23f8

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution {O : Type} [CommRing O] {ι : Type} [Fintype ι] [DecidableEq ι] {Nb : ι → Type}
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (a : ι) (y : ⨂[O] τ, Nb τ) :
    atFactor a (LinearMap.id : Nb a →ₗ[O] Nb a) y = y := by
  unfold atFactor
  rw [Function.update_eq_self a (fun τ => (LinearMap.id : Nb τ →ₗ[O] Nb τ)), PiTensorProduct.map_id]
  rfl
end Formalism.CohomologicalDescent.DepthNonnegative
