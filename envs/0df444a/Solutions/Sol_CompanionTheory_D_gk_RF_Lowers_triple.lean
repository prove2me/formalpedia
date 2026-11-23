-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.Lowers.triple
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:11.766274+00:00
-- url     : https://prove2.me/submissions/167d85ff-bd14-415b-9c98-38fd1ee446e0

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation
import Theorems.Thm_CompanionTheory_D_gk_RF_mat_extC

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
namespace Lowers
theorem _root_.solution {A B C : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (hB : Lowers J W B)
    (hC : Lowers J W C) : A * (B * C) = 0 :=
  mat_extC fun z => by rw [← mulVec_mulVec, ← mulVec_mulVec, hA.1 _ (hB.2.1 _ (hC.2.2 z)), zero_mulVec]
end Lowers
end CompanionTheory.D.gk.RF
