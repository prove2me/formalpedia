-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.sum_lat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:44.602708+00:00
-- url     : https://prove2.me/submissions/8606fcde-5cbb-4afa-82e3-13bd1554ef00

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_lat_succ

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
theorem _root_.solution (g : ℕ → ℝ) (q : ℕ → Bool) (B : ℕ → ℕ) : ∀ n,
    ∑ l ∈ range (lat q B n).length, g ((lat q B n).getD l 0) =
      ∑ i ∈ (Icc 1 n).filter (fun i => q i = true), g (B i)
  | 0 => by simp [lat]
  | n + 1 => by
      rw [lat_succ, Finset.sum_filter, Finset.sum_Icc_succ_top (by omega), ← Finset.sum_filter,
        ← solution g q B n]
      by_cases h : q (n + 1) = true
      · simp only [if_pos h, List.length_cons, Finset.sum_range_succ', List.getD_cons_succ,
          List.getD_cons_zero]
      · simp only [if_neg h, add_zero]
end Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
