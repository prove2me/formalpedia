-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.tensor_projection_kill_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:19:42.121015+00:00
-- url     : https://prove2.me/submissions/782cc810-519c-4df7-830a-af9d29008b04

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
open CategoryTheory CategoryTheory.Limits
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution : TensorProjKill := by
  intro R _ P X P' _ _ _ _ _ _ p l c h z
  have h1 : ∀ y : X ⊗[R] P', l ^ c • TensorProduct.map p (LinearMap.id : P' →ₗ[R] P') y = 0 := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => rw [TensorProduct.map_tmul, TensorProduct.smul_tmul', h x, TensorProduct.zero_tmul]
    | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [TensorProduct.map_tmul, ← TensorProduct.tmul_smul, h1 y, TensorProduct.tmul_zero]
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]
end Formalism.CohomologicalDescent.DepthNonnegative
