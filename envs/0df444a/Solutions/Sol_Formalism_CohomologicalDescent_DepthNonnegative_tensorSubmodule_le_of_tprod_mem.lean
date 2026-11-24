-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.tensorSubmodule_le_of_tprod_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:11:33.418835+00:00
-- url     : https://prove2.me/submissions/40ba7f2a-386b-4330-b5d5-4ba6082e2bae

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
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ))
    (U : Submodule O (⨂[O] τ, Nb τ))
    (h : ∀ x : ∀ τ, Nb τ, (∀ τ, x τ ∈ B τ) → PiTensorProduct.tprod O x ∈ U) : tensSub B ≤ U := by
  rintro _ ⟨z, rfl⟩
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r u =>
    rw [map_smul, PiTensorProduct.map_tprod]
    exact U.smul_mem _ (h _ fun τ => (u τ).2)
  | add a b ha hb =>
    rw [map_add]
    exact U.add_mem ha hb
end Formalism.CohomologicalDescent.DepthNonnegative
