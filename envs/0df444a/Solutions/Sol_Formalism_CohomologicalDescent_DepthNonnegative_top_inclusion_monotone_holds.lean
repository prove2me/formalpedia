-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.top_inclusion_monotone_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:23:51.366916+00:00
-- url     : https://prove2.me/submissions/da8ed30f-3626-4e8a-875e-68744b9e9746

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


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
theorem _root_.solution : TopInclMono := by
  intro O _ A _ _ G _ Γ K jK ι l N lam _ _ T _ _ _ _ S J J' hJ h y
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hJ
  obtain ⟨x, hx, s, hxs⟩ := h y
  refine ⟨(algebraMap O T (l : O)) ^ d • x, ?_, s, ?_⟩
  · show (((algebraMap O T (l : O)) ^ d • x : Forms O Γ jK (NablaT O N lam)) : G → NablaT O N lam) ∈
      formsIn Γ K (repOf O jK (NablaT O N lam)) (tensSub (deltaIn O N lam))
    rw [← map_pow, algebraMap_smul]
    exact Submodule.smul_mem _ _ hx
  · rw [← LocalizedModule.smul'_mk, hxs, smul_smul, ← pow_add, add_comm]
end Formalism.CohomologicalDescent.DepthNonnegative
