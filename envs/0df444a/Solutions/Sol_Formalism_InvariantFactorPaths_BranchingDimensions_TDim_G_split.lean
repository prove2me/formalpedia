-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TDim.G_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:11.81843+00:00
-- url     : https://prove2.me/submissions/c4cb7500-283d-47bb-806d-24408e330c3b

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogWeylDimensionEstimate
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_hh_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_dom_anti
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_G_eq

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
theorem _root_.solution {n : ℕ} {la : ℕ → ℤ} (hd : Dom n la) {i j : ℕ} (hij : i < j) (hj : j < n) :
    G la i j = pa la i j + pb la i j + pc la i j := by
  have hle : la j ≤ la i := dom_anti hd hij.le hj
  unfold pa pb pc
  rw [G_eq hij]
  by_cases hi0 : la i = 0 <;> by_cases hj0 : la j = 0
  · rw [if_neg (show ¬(la i ≠ 0 ∧ la j ≠ 0) from fun h => h.1 hi0), if_pos hj0, if_pos hi0,
      hi0, hj0]
    simp [hh_zero]
  · have hm : max (-(la j)) 0 = la i - la j := by
      rw [hi0, max_eq_left (show (0 : ℤ) ≤ -la j by linarith)]
      ring
    rw [if_neg (show ¬(la i ≠ 0 ∧ la j ≠ 0) from fun h => h.1 hi0), if_neg hj0, if_pos hi0, hm]
    ring
  · have hm : max (la i) 0 = la i - la j := by
      rw [hj0, sub_zero]
      exact max_eq_left (by linarith)
    rw [if_neg (show ¬(la i ≠ 0 ∧ la j ≠ 0) from fun h => h.2 hj0), if_pos hj0, if_neg hi0, hm]
    ring
  · rw [if_pos ⟨hi0, hj0⟩, if_neg hj0, if_neg hi0]
    ring
end Formalism.InvariantFactorPaths.BranchingDimensions.TDim
