-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.middle_top_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:48:34.222801+00:00
-- url     : https://prove2.me/submissions/605bd1b9-f58a-46e0-bd73-c9de4c94d5b2

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_midGen_top
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_span_map_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution : MidTop := by
  intro p _ N r _ D
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨j, jp, hok, x, hx, rfl⟩
    rw [SetLike.mem_coe, cm_midGen_top, ← LinearMap.mulLeft_apply (R := ℚ_[p])]
    refine span_map_mem _ _ _ ?_ x hx
    rintro _ ⟨y, hy, g, hg, rfl⟩
    refine Submodule.subset_span ?_
    simp only [Set.mem_iUnion]
    exact ⟨j, jp, hok, y, hy, g, hg, by rw [LinearMap.mulLeft_apply, mul_assoc _ (rename _ y) g]⟩
  · refine Submodule.span_le.mpr ?_
    intro v hv
    simp only [Set.mem_iUnion] at hv
    obtain ⟨j, jp, hok, y, hy, g, hg, rfl⟩ := hv
    refine Submodule.subset_span ⟨j, jp, hok, rename (chainEmb N r D.T.t) y * g,
      Submodule.subset_span ⟨y, hy, g, hg, rfl⟩, ?_⟩
    rw [cm_midGen_top, mul_assoc _ (rename _ y) g]
end Formalism.InvariantFactorPaths.KP.LL
