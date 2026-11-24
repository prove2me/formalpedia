-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:49.21074+00:00
-- url     : https://prove2.me/submissions/d9e98fab-07d1-4e59-96b9-82de9cedf907

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_lat_split
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
namespace TTyp
end TTyp
namespace TTyp
end TTyp
namespace TTyp
private theorem list_getD_append_add_length (pre R : List ℕ) (u : ℕ) : (pre ++ R).getD (u + pre.length) 0 = R.getD u 0 := by
  induction pre with
  | nil => simp
  | cons x pre ih =>
    rw [List.length_cons, ← Nat.add_assoc, List.cons_append, List.getD_cons_succ]
    exact ih
end TTyp
namespace TTyp
end TTyp
end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
open Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
namespace Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
theorem _root_.solution (q : ℕ → Bool) (B : ℕ → ℕ) {i n : ℕ} (h : i ≤ n) :
    (∀ u, (lat q B n).getD (u + ((Icc (i + 1) n).filter (fun l => q l = true)).card) 0 =
      (lat q B i).getD u 0) ∧
    (lat q B n).length = ((Icc (i + 1) n).filter (fun l => q l = true)).card + (lat q B i).length := by
  obtain ⟨pre, hpre, hlen⟩ := lat_split q B i (n - i)
  rw [show i + (n - i) = n by omega] at hpre hlen
  refine ⟨fun u => ?_, ?_⟩
  · rw [hpre, ← hlen, list_getD_append_add_length]
  · rw [hpre, List.length_append, hlen]
end Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
