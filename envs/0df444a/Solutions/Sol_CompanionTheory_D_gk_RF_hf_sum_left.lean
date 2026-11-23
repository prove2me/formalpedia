-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.hf_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:22.268137+00:00
-- url     : https://prove2.me/submissions/e879d499-2c6f-46c1-81fe-c2595bb00abe

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
theorem _root_.solution {ι : Type} (s : Finset ι) (x : ι → Fin n → K) (y : Fin n → K) :
    hf J (∑ i ∈ s, x i) y = ∑ i ∈ s, hf J (x i) y := by
  simp only [hf, star_sum, sum_dotProduct]
end CompanionTheory.D.gk.RF
