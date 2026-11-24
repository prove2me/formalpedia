-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:32.070029+00:00
-- url     : https://prove2.me/submissions/96b8fde6-ec7a-461e-a4fb-6a76f47f302e

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
theorem _root_.solution (q : ℕ → Bool) (B : ℕ → ℕ) (i : ℕ) : ∀ d, ∃ pre : List ℕ,
    lat q B (i + d) = pre ++ lat q B i ∧
    pre.length = ((Icc (i + 1) (i + d)).filter (fun l => q l = true)).card
  | 0 => ⟨[], by simp, by simp⟩
  | d + 1 => by
      obtain ⟨pre, h1, h2⟩ := solution q B i d
      rw [← add_assoc, lat_succ, Finset.card_filter, Finset.sum_Icc_succ_top (by omega),
        ← Finset.card_filter]
      by_cases h : q (i + d + 1) = true
      · exact ⟨B (i + d + 1) :: pre, by simp [h, h1], by simp [h, h2]⟩
      · exact ⟨pre, by simp [h, h1], by simp [h, h2]⟩
end Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
