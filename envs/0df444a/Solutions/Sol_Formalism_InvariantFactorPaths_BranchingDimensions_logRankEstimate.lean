-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.logRankEstimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:43:51.921729+00:00
-- url     : https://prove2.me/submissions/946480df-6d25-4774-84a1-b42a22e9ab69

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogBinomialProperties
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_fT_nat
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_fT_add_bounds

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
theorem _root_.solution : LogRankEstimate := by
  intro D A0 hA0 hr hrN hK hB
  obtain ⟨d, hd, hdle⟩ : ∃ d : ℕ, D.k - 1 = D.k' + d ∧ d ≤ D.r + 2 * D.Ns := by
    refine ⟨D.r + 2 * D.Ns - 1, ?_, by omega⟩
    unfold Letters.k Letters.k'
    omega
  have hk1 : 1 ≤ D.k := by unfold Letters.k; omega
  have hlog : Real.log (D.rankAA : ℝ) = ∑ i ∈ Icc 1 D.n0, fT (D.k' + d) (D.B i) := by
    unfold Letters.rankAA
    rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro i _
      rw [fT_nat, ← hd]
      have : D.B i + D.k - 1 = D.B i + (D.k - 1) := by omega
      rw [this]
    · intro i _
      have : 0 < (D.B i + D.k - 1).choose (D.k - 1) := Nat.choose_pos (by omega)
      exact_mod_cast this.ne'
  rw [hlog, ← Finset.sum_sub_distrib]
  have hl0 : 0 ≤ Real.log (1 + A0) := Real.log_nonneg (by linarith)
  constructor
  · apply Finset.sum_nonneg
    intro i _
    exact (fT_add_bounds D.k' (D.B i) (Nat.cast_nonneg _) d).1
  · have h1 : ∑ i ∈ Icc 1 D.n0, (fT (D.k' + d) (D.B i) - fT D.k' (D.B i)) ≤
        ∑ _i ∈ Icc 1 D.n0, ((D.r : ℝ) + 2 * D.Ns) * Real.log (1 + A0) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hBi : (0 : ℝ) ≤ (D.B i : ℝ) := Nat.cast_nonneg _
      refine le_trans (fT_add_bounds D.k' (D.B i) hBi d).2 ?_
      have hdR : (d : ℝ) ≤ (D.r : ℝ) + 2 * D.Ns := by exact_mod_cast hdle
      have hll : Real.log (1 + (D.B i : ℝ)) ≤ Real.log (1 + A0) :=
        Real.log_le_log (by linarith) (by linarith [hB i hi'.1 hi'.2])
      exact mul_le_mul hdR hll (Real.log_nonneg (by linarith)) (by positivity)
    refine le_trans h1 ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_assoc]
    have hn : ((D.n0 + 1 - 1 : ℕ) : ℝ) ≤ (D.Ns : ℝ) := by
      have : D.n0 + 1 - 1 ≤ D.Ns := by unfold Letters.n0; omega
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hn (by positivity)
end Formalism.InvariantFactorPaths.BranchingDimensions
