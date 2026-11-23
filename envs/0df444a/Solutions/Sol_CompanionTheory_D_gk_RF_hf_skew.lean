-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.hf_skew
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:26.72238+00:00
-- url     : https://prove2.me/submissions/87bedad9-6311-4053-a7fd-4cac99ce989b

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation
import Theorems.Thm_CompanionTheory_D_gk_RF_skew_eq

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
theorem _root_.solution {X : Matrix (Fin n) (Fin n) K} (h : Xᴴ * J + J * X = 0) (x y : Fin n → K) :
    hf J (X *ᵥ x) y = -hf J x (X *ᵥ y) := by
  unfold hf
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, skew_eq h, neg_mulVec, dotProduct_neg, mulVec_mulVec]
end CompanionTheory.D.gk.RF
