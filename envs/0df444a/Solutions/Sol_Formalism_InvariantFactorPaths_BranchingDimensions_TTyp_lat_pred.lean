-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat_pred
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:32.049561+00:00
-- url     : https://prove2.me/submissions/fd63f899-1c80-4fd9-8a75-636c27e1953c

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
theorem _root_.solution (q : ℕ → Bool) (B : ℕ → ℕ) {i : ℕ} (hi : 1 ≤ i) (h : q i = false) :
    lat q B (i - 1) = lat q B i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [lat_succ, if_neg (by simp [h]), Nat.add_sub_cancel]
end Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
