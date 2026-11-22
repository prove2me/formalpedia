-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.htMap_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:21:51.270254+00:00
-- url     : https://prove2.me/submissions/b430fad2-7a7d-4c01-add0-76bef78bb7b3

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
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (φ : V →ₗ[K] W) (B : ℝ) (hB : 1 ≤ B)
    (h : ∀ v, opNormAt b X b' X' v φ ≤ B) : htMap b X b' X' φ ≤ 2 * Real.log B := by
  show (1 / (nPl K : ℝ)) * ∑ v, Real.log (opNormAt b X b' X' v φ ^ 2) ≤ 2 * Real.log B
  have hterm : ∀ v, Real.log (opNormAt b X b' X' v φ ^ 2) ≤ 2 * Real.log B := by
    intro v
    have hx0 : 0 ≤ opNormAt b X b' X' v φ := norm_nonneg _
    have h2 : Real.log (B ^ 2) = 2 * Real.log B := by
      rw [Real.log_pow]
      norm_num
    rw [← h2]
    rcases eq_or_lt_of_le (sq_nonneg (opNormAt b X b' X' v φ)) with h0 | h0
    · rw [← h0, Real.log_zero]
      exact Real.log_nonneg (by nlinarith)
    · exact Real.log_le_log h0 (by nlinarith [h v])
  rcases Nat.eq_zero_or_pos (nPl K) with h0 | hpos
  · rw [h0, Nat.cast_zero, div_zero, zero_mul]
    exact mul_nonneg zero_le_two (Real.log_nonneg hB)
  · have hn : (0 : ℝ) < nPl K := by exact_mod_cast hpos
    have hne : (nPl K : ℝ) ≠ 0 := hn.ne'
    calc (1 / (nPl K : ℝ)) * ∑ v, Real.log (opNormAt b X b' X' v φ ^ 2)
        ≤ (1 / (nPl K : ℝ)) * ∑ _v : InfinitePlace K, 2 * Real.log B := by
          gcongr with v _
          exact hterm v
      _ = 2 * Real.log B := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hc : (nPl K : ℝ) = (Fintype.card (InfinitePlace K) : ℝ) := rfl
          rw [← hc, one_div, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
end Formalism.BranchingDeterminantCap.PrismTransfer
