-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.mem_lat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:44.562504+00:00
-- url     : https://prove2.me/submissions/3f4962ab-0b7e-4943-aae8-82d057490a92

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf

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
open Letters
open Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
namespace Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
theorem _root_.solution {q : ℕ → Bool} {B : ℕ → ℕ} {j x : ℕ} (h : x ∈ lat q B j) :
    ∃ l, 1 ≤ l ∧ l ≤ j ∧ q l = true ∧ x = B l := by
  unfold lat at h
  simp only [List.mem_map, List.mem_reverse, List.mem_filter, List.mem_range'_1] at h
  obtain ⟨l, ⟨⟨h1, h2⟩, hq⟩, hx⟩ := h
  exact ⟨l, h1, by omega, hq, hx.symm⟩
end Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
