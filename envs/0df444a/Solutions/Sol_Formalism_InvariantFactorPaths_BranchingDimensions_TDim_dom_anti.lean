-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TDim.dom_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:28.190795+00:00
-- url     : https://prove2.me/submissions/5e0f171a-dc66-49da-a4f2-b0c184a20029

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogWeylDimensionEstimate

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
theorem _root_.solution {n : ℕ} {la : ℕ → ℤ} (h : Dom n la) {i j : ℕ} (hij : i ≤ j) (hj : j < n) :
    la j ≤ la i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  revert hj
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hj
    have h1 := h (i + k) (by omega)
    have h2 := ih (by omega)
    show la (i + k + 1) ≤ la i
    exact h1.trans h2
end Formalism.InvariantFactorPaths.BranchingDimensions.TDim
