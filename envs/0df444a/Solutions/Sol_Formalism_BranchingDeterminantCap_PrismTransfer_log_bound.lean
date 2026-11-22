-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.log_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:21:59.46281+00:00
-- url     : https://prove2.me/submissions/fc1ce4fe-2edf-4151-84ee-3a93dc259f0b

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
open PrismTransfer
open Formalism.BranchingDeterminantCap.PrismTransfer
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
variable {W κ : Type} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]
namespace Formalism.BranchingDeterminantCap.PrismTransfer
theorem _root_.solution (G n : ℕ) (hG : 0 < G) (hn : 0 < n) :
    1 ≤ (G : ℝ) ^ 3 * Real.sqrt n ∧
      2 * Real.log ((G : ℝ) ^ 3 * Real.sqrt n) = 6 * Real.log G + Real.log n := by
  have hG1 : (1 : ℝ) ≤ G := by exact_mod_cast hG
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hG0 : (0 : ℝ) < G := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 : (1 : ℝ) ≤ (G : ℝ) ^ 3 := one_le_pow₀ hG1
  have h2 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hn1
  refine ⟨one_le_mul_of_one_le_of_one_le h1 h2, ?_⟩
  rw [Real.log_mul (pow_pos hG0 3).ne' (Real.sqrt_pos.mpr hn0).ne', Real.log_pow,
    Real.log_sqrt hn0.le]
  push_cast
  ring
end Formalism.BranchingDeterminantCap.PrismTransfer
