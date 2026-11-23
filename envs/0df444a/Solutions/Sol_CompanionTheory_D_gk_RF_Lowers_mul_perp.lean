-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.Lowers.mul_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:55.892897+00:00
-- url     : https://prove2.me/submissions/c51705d5-c18e-45d3-b026-2dcc84298f55

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
theorem _root_.solution {A B : Matrix (Fin n) (Fin n) K} (hA : Lowers J W A) (hB : Lowers J W B) :
    (∀ z ∈ perp J W, (A * B) *ᵥ z = 0) ∧ ∀ z, (A * B) *ᵥ z ∈ W :=
  ⟨fun z hz => by rw [← mulVec_mulVec, hA.1 _ (hB.2.1 z hz)],
    fun z => by rw [← mulVec_mulVec]; exact hA.2.1 _ (hB.2.2 z)⟩
end Lowers
end CompanionTheory.D.gk.RF
