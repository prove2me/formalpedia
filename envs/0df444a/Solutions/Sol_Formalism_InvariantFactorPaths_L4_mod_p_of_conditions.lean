-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.mod_p_of_conditions
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:52.297362+00:00
-- url     : https://prove2.me/submissions/1c98624b-3a7d-480f-b6e2-575986b3b080

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_of_stable
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_glStable
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_le_supp
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : ModOfY := by
  intro p _ N r _ LL j M h hh
  refine modCond_of_stable p LL j M (YCond p (r := r) LL j M : Set _) ?_ ?_ h hh
  · intro x hx c _ k
    simp only [dpow, LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    induction k with
    | zero => exact hx
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact ycond_glStable LL j M 0 c _ ih
  · intro x hx m hm
    have h1 := ycond_le_supp LL j M hx
    rw [mem_restrictSupport_iff] at h1
    have : coeff m x = 0 := by
      by_contra hne
      exact hm (h1 (Finset.mem_coe.mpr (mem_support_iff.mpr hne)))
    rw [this, norm_zero]
    exact one_pos
end Formalism.InvariantFactorPaths.L4
