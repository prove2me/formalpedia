-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.Lowers.smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:35.4198+00:00
-- url     : https://prove2.me/submissions/3f03852d-b707-4ef6-9a55-127c7d0c8fd5

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
namespace Lowers
theorem _root_.solution {A : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (c : K) : Lowers J W (c • A) :=
  ⟨fun w hw => by rw [smul_mulVec, hA.1 w hw, smul_zero],
    fun z hz => by rw [smul_mulVec]; exact W.smul_mem c (hA.2.1 z hz),
    fun z => by rw [smul_mulVec]; exact (perp J W).smul_mem c (hA.2.2 z)⟩
end Lowers
end CompanionTheory.D.gk.RF
