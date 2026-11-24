-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.tail_pos_shift_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:14.92087+00:00
-- url     : https://prove2.me/submissions/45672472-2ac6-4387-ad23-c67e21cb5c3a

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tailPos_succ

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
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (a b : ℕ → ℤ) (u : ℕ) :
    ∀ n, (∀ m, m + 1 < n + 1 → b (m + 1) ≤ a m) → tailPos (n + 1) b (u + 1) ≤ tailPos n a u := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [tailPos, Finset.filter_singleton]
  | succ n ih =>
    intro h
    rw [tailPos_succ (n + 1) b, tailPos_succ n a]
    have h1 := ih (fun m hm => h m (by omega))
    have h2 : b (n + 1) ≤ a n := h n (by omega)
    have h3 : max (b (n + 1)) 0 ≤ max (a n) 0 := max_le_max h2 le_rfl
    have hiff : (u + 1 ≤ n + 1) ↔ (u ≤ n) := by omega
    simp only [hiff]
    split_ifs <;> linarith
end Formalism.InvariantFactorPaths.BranchingDimensions
