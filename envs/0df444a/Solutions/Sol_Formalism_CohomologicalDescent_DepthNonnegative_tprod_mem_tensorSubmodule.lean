-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.tprod_mem_tensorSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:13:31.75664+00:00
-- url     : https://prove2.me/submissions/a00999d5-c802-42bf-8045-b673a9241e05

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
theorem _root_.solution {O : Type} [CommRing O] {ι : Type} [Fintype ι] {Nb : ι → Type}
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)) (x : ∀ τ, Nb τ)
    (hx : ∀ τ, x τ ∈ B τ) : PiTensorProduct.tprod O x ∈ tensSub B := by
  refine ⟨PiTensorProduct.tprod O (fun τ => (⟨x τ, hx τ⟩ : B τ)), ?_⟩
  rw [PiTensorProduct.map_tprod]
  rfl
end Formalism.CohomologicalDescent.DepthNonnegative
