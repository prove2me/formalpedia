-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.fT_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:59.718932+00:00
-- url     : https://prove2.me/submissions/24a9aef8-a0c9-4d36-a956-5a8872d933ab

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogBinomialProperties
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_fT_succ

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
theorem _root_.solution (k' y : ℕ) : fT k' y = Real.log ((y + k').choose k') := by
  induction k' with
  | zero => simp [fT]
  | succ n ih =>
    have hc : (0 : ℝ) < ((y + n).choose n : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.le_add_left n y)
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hy : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
    rw [fT_succ, ih, ← Real.log_mul hc.ne' (by positivity)]
    congr 1
    have h := Nat.add_one_mul_choose_eq (y + n) n
    have h' : (((y + n).succ : ℕ) : ℝ) * ((y + n).choose n : ℝ) =
        (((y + n).succ.choose n.succ : ℕ) : ℝ) * ((n.succ : ℕ) : ℝ) := by exact_mod_cast h
    have e1 : (((y + n).succ : ℕ) : ℝ) = (y : ℝ) + ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e1] at h'
    have e2 : y + (n + 1) = (y + n).succ := rfl
    rw [e2, mul_div_assoc', eq_comm, eq_div_iff hn.ne', ← h', mul_comm]
end Formalism.InvariantFactorPaths.BranchingDimensions
