-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.hf_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:44.032907+00:00
-- url     : https://prove2.me/submissions/8c665d42-7637-4a1f-8862-8fd35071bca3

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation

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
theorem _root_.solution (hJ : Jᴴ = J) (x y : Fin n → K) : star (hf J x y) = hf J y x := by
  unfold hf
  rw [← star_dotProduct_star, star_star, star_mulVec, hJ, dotProduct_mulVec]
end CompanionTheory.D.gk.RF
