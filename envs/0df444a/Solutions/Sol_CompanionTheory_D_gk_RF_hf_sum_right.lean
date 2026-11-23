-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.hf_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:22.611819+00:00
-- url     : https://prove2.me/submissions/50b6471b-9308-4b1a-b2a4-773d24c8b461

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
theorem _root_.solution {ι : Type} (s : Finset ι) (x : Fin n → K) (y : ι → Fin n → K) :
    hf J x (∑ i ∈ s, y i) = ∑ i ∈ s, hf J x (y i) := by
  simp only [hf, mulVec_sum, dotProduct_sum]
end CompanionTheory.D.gk.RF
