-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TDim.neg_idx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:05.230814+00:00
-- url     : https://prove2.me/submissions/4263e013-55ad-4f36-94f7-1aa5b55d34da

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogWeylDimensionEstimate
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_dom_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Formalism.InvariantFactorPaths.BranchingDimensions.TDim
namespace Formalism.InvariantFactorPaths.BranchingDimensions.TDim
theorem _root_.solution {n Ns : ℕ} {la : ℕ → ℤ} (h : Dom n la)
    (hc : ((range n).filter fun m => la m < 0).card ≤ Ns) {t : ℕ} (ht : t < n) (hp : la t < 0) :
    n ≤ t + Ns := by
  have hsub : Ico t n ⊆ (range n).filter fun m => la m < 0 := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hm.2, lt_of_le_of_lt (dom_anti h hm.1 hm.2) hp⟩
  have := Finset.card_le_card hsub
  rw [Nat.card_Ico] at this
  omega
end Formalism.InvariantFactorPaths.BranchingDimensions.TDim
