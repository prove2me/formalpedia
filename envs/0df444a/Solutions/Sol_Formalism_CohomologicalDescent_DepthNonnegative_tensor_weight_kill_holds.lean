-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.tensor_weight_kill_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:31:30.081796+00:00
-- url     : https://prove2.me/submissions/000fc6dd-cce8-4260-9b6b-61e60f3cf3e3

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_factor_action_on_tensor_product_holds
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_tprod_mem_tensorSubmodule
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_tensorSubmodule_le_of_tprod_mem
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
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution : TensorWeightKill := by
  intro O _ ι _ _ Nb _ _ B s a p l c ha hp
  have key : tensSub (chainB B (insert a s)) ≤
      (tensSub (chainB B s)).comap ((l ^ c) • atFactor a p) := by
    apply tensorSubmodule_le_of_tprod_mem
    intro x hx
    rw [Submodule.mem_comap, LinearMap.smul_apply, factor_action_on_tensor_product_holds,
      ← MultilinearMap.map_update_smul]
    try rw [Function.update_idem]
    apply tprod_mem_tensorSubmodule
    intro τ
    by_cases h : τ = a
    · subst h
      simp only [Function.update_self, chainB, if_neg ha]
      exact hp _
    · rw [Function.update_of_ne h]
      have h1 := hx τ
      simp only [chainB, Finset.mem_insert, h, false_or] at h1 ⊢
      exact h1
  intro y hy
  exact key hy
end Formalism.CohomologicalDescent.DepthNonnegative
