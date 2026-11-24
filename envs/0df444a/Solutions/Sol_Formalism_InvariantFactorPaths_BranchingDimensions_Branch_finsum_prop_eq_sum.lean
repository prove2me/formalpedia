-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.Branch.finsum_prop_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:31.905627+00:00
-- url     : https://prove2.me/submissions/abdc3c18-3ba5-467e-a0f4-c9022404b5e5

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch

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
open Formalism.InvariantFactorPaths.BranchingDimensions.Branch
namespace Formalism.InvariantFactorPaths.BranchingDimensions.Branch
theorem _root_.solution {α : Type*} (p : α → Prop) (s : Finset α) (f : α → ℝ) (h : ∀ a, p a ↔ a ∈ s) :
    ∑ᶠ (a : α) (_ : p a), f a = ∑ a ∈ s, f a := by
  rw [← finsum_mem_coe_finset]
  refine finsum_congr fun a => ?_
  have e : p a = (a ∈ (s : Set α)) := propext (by rw [Finset.mem_coe]; exact h a)
  rw [e]
end Formalism.InvariantFactorPaths.BranchingDimensions.Branch
