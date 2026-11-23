-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.Lowers.neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:26.073683+00:00
-- url     : https://prove2.me/submissions/8733466a-add6-4396-afd9-751a0cb5a2e2

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation
import Theorems.Thm_CompanionTheory_D_gk_RF_Lowers_smul

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
theorem _root_.solution {A : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) : Lowers J W (-A) := by
  simpa using hA.smul (-1)
end Lowers
end CompanionTheory.D.gk.RF
