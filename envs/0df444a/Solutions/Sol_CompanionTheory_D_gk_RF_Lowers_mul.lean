-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.Lowers.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:58.92801+00:00
-- url     : https://prove2.me/submissions/7edd0a51-0282-416a-93ba-6e0c9fb15f13

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation
import Theorems.Thm_CompanionTheory_D_gk_RF_Lowers_mul_perp
import Theorems.Thm_CompanionTheory_D_gk_RF_lowers_of_Z

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
theorem _root_.solution (hW : Isot J W) {A B : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (hB : Lowers J W B) :
    Lowers J W (A * B) := lowers_of_Z hW (hA.mul_perp hB).1 (hA.mul_perp hB).2
end Lowers
end CompanionTheory.D.gk.RF
