-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:35:35.893609+00:00
-- url     : https://prove2.me/submissions/47056ffe-41ab-4d72-b764-a2e3edcfb08c

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf
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
private theorem list_range'_succ_eq_append_singleton (s n : ℕ) : List.range' s (n + 1) = List.range' s n ++ [s + n] := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    show s :: List.range' (s + 1) (n + 1) = (s :: List.range' (s + 1) n) ++ [s + (n + 1)]
    rw [ih (s + 1), show s + 1 + n = s + (n + 1) by omega]
    rfl
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
theorem _root_.solution (q : ℕ → Bool) (B : ℕ → ℕ) (i : ℕ) :
    lat q B (i + 1) = if q (i + 1) = true then B (i + 1) :: lat q B i else lat q B i := by
  unfold lat
  rw [list_range'_succ_eq_append_singleton, show (1 : ℕ) + i = i + 1 from Nat.add_comm 1 i, List.filter_append]
  by_cases hq : q (i + 1) = true
  · simp [hq]
  · simp [hq]
end Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
