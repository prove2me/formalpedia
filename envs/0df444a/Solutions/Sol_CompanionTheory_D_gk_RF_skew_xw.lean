-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.skew_xw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:32.339909+00:00
-- url     : https://prove2.me/submissions/4248740f-2d98-4776-a1bf-878d4ae33a25

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation
import Theorems.Thm_CompanionTheory_D_gk_RF_xw_mulVec
import Theorems.Thm_CompanionTheory_D_gk_RF_hf_star
import Theorems.Thm_CompanionTheory_D_gk_RF_hf_sub_right
import Theorems.Thm_CompanionTheory_D_gk_RF_hf_smul_right
import Theorems.Thm_CompanionTheory_D_gk_RF_hf_add_leftC
import Theorems.Thm_CompanionTheory_D_gk_RF_hf_neg_left
import Theorems.Thm_CompanionTheory_D_gk_RF_hf_smul_leftC
import Theorems.Thm_CompanionTheory_D_gk_RF_skew_of_hf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.RF
variable {K : Type} [Field K] [StarRing K] {n : ℕ} {J : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)}
namespace CompanionTheory.D.gk.RF
theorem _root_.solution (hJ : Jᴴ = J) (w b : Fin n → K) : (xw J w b)ᴴ * J + J * xw J w b = 0 :=
  skew_of_hf fun x y => by
    rw [xw_mulVec, xw_mulVec, sub_eq_add_neg, hf_add_leftC, hf_neg_left, hf_smul_leftC, hf_smul_leftC, hf_sub_right,
      hf_smul_right, hf_smul_right, hf_star hJ, hf_star hJ]
    ring
end CompanionTheory.D.gk.RF
