-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.middle_p_eq_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:18.262836+00:00
-- url     : https://prove2.me/submissions/ea41b8d9-f31f-4683-8a10-0ec67f1bac30

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_PLL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_PplusL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_Pall_eq
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
theorem _root_.solution : MidPEq := by
  intro p _ N r _ D
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨j, jp, hok, x, hx, rfl⟩
    have key : ∀ x' : MvPolynomial (BVar N r D.T.t) ℚ_[p],
        ((LinearMap.mulLeft ℚ_[p] ((∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp) *
          (cmPplusL p D jp * cmPLL p D (List.finRange D.T.t) j jp) :
            Module.End ℚ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]))) x' =
        (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
          Pplus p D jp (PL p D (List.finRange D.T.t) j jp x') := by
      intro x'
      rw [Module.End.mul_apply, Module.End.mul_apply, cm_PLL_apply, cm_PplusL_apply, LinearMap.mulLeft_apply]
    rw [SetLike.mem_coe, ← key]
    refine span_map_mem _ _ _ ?_ x hx
    rintro _ ⟨y, hy, g, hg, rfl⟩
    refine Submodule.subset_span ?_
    simp only [Set.mem_iUnion]
    exact ⟨j, jp, hok, y, hy, g, hg, by rw [key, Pall_eq]⟩
  · refine Submodule.span_le.mpr ?_
    intro v hv
    simp only [Set.mem_iUnion] at hv
    obtain ⟨j, jp, hok, y, hy, g, hg, rfl⟩ := hv
    exact Submodule.subset_span ⟨j, jp, hok, rename (chainEmb N r D.T.t) y * g,
      Submodule.subset_span ⟨y, hy, g, hg, rfl⟩, by rw [Pall_eq]⟩
end Formalism.InvariantFactorPaths.KP.LL
