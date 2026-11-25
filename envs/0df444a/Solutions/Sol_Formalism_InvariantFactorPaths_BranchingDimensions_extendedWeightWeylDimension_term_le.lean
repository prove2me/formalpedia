-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:05:51.46346+00:00
-- url     : https://prove2.me/submissions/9e34b9ad-7d6a-4f40-8275-5b468b1afb45

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_TTotal

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
open Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
namespace Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
theorem _root_.solution {n : ℕ} {a b : ℕ → ℤ} (h : ∀ m, m < n → a m ≤ b m) {m : ℕ} (hm : m < n) :
    b m - a m ≤ wsize n b - wsize n a := by
  unfold wsize
  rw [← Finset.sum_sub_distrib]
  exact Finset.single_le_sum (f := fun m => b m - a m)
    (fun i hi => sub_nonneg.2 (h i (mem_range.1 hi))) (mem_range.2 hm)
end Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
