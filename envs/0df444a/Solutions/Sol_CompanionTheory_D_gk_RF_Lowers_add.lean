-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.Lowers.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:34.869964+00:00
-- url     : https://prove2.me/submissions/15064d55-d6e6-46a0-8c2f-6033194f01b7

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
theorem _root_.solution {A B : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (hB : Lowers J W B) : Lowers J W (A + B) :=
  ⟨fun w hw => by rw [add_mulVec, hA.1 w hw, hB.1 w hw, add_zero],
    fun z hz => by rw [add_mulVec]; exact W.add_mem (hA.2.1 z hz) (hB.2.1 z hz),
    fun z => by rw [add_mulVec]; exact (perp J W).add_mem (hA.2.2 z) (hB.2.2 z)⟩
end Lowers
end CompanionTheory.D.gk.RF
