-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pos_idx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:17.443825+00:00
-- url     : https://prove2.me/submissions/a650d7f5-e02d-495c-9bb0-23fadb6c99d3

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
    (hc : ((range n).filter fun m => 0 < la m).card ≤ Ns) {i : ℕ} (hi : i < n) (hp : 0 < la i) :
    i < Ns := by
  have hsub : range (i + 1) ⊆ (range n).filter fun m => 0 < la m := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, lt_of_lt_of_le hp (dom_anti h (by omega) hi)⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  omega
end Formalism.InvariantFactorPaths.BranchingDimensions.TDim
