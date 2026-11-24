-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.fT_add_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:13.131716+00:00
-- url     : https://prove2.me/submissions/34f6d6f1-e7b8-4e1d-8e8a-b39b55a4a9b3

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
theorem _root_.solution (k' : ℕ) (y : ℝ) (hy : 0 ≤ y) (d : ℕ) :
    0 ≤ fT (k' + d) y - fT k' y ∧ fT (k' + d) y - fT k' y ≤ (d : ℝ) * Real.log (1 + y) := by
  induction d with
  | zero => simp
  | succ n ih =>
    have hN : (1 : ℝ) ≤ ((k' + n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hN0 : (0 : ℝ) < ((k' + n + 1 : ℕ) : ℝ) := by linarith
    have e : fT (k' + (n + 1)) y = fT (k' + n) y +
        Real.log ((y + ((k' + n + 1 : ℕ) : ℝ)) / ((k' + n + 1 : ℕ) : ℝ)) := fT_succ (k' + n) y
    have h1 : 1 ≤ (y + ((k' + n + 1 : ℕ) : ℝ)) / ((k' + n + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hN0]; linarith
    have h2 : (y + ((k' + n + 1 : ℕ) : ℝ)) / ((k' + n + 1 : ℕ) : ℝ) ≤ 1 + y := by
      rw [div_le_iff₀ hN0]
      nlinarith [mul_nonneg hy (sub_nonneg.mpr hN)]
    have l1 := Real.log_nonneg h1
    have l2 := Real.log_le_log (by linarith) h2
    have ec : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [e, ec]
    constructor
    · linarith [ih.1]
    · linarith [ih.2]
end Formalism.InvariantFactorPaths.BranchingDimensions
