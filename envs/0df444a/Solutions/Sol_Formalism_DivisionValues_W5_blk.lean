-- Prove2me | solution 1 for Formalism.DivisionValues.W5.blk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:19.738904+00:00
-- url     : https://prove2.me/submissions/8e9fd1f3-7f54-4cb5-ae93-06609d64f69b

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_UntwistedChoice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Theorems.Thm_Formalism_DivisionValues_W5_tele
import Theorems.Thm_Formalism_DivisionValues_W5_exp_two_le
import Theorems.Thm_Formalism_DivisionValues_W5_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.W5
namespace Formalism.DivisionValues.W5
theorem _root_.solution (K : ℕ) (hK : 40 ≤ K) :
    ∑ n ∈ Finset.Ico 240 (6 * K),
      (if n % 6 = 1 ∨ n % 6 = 5 then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) ≤
    ((Real.log 234 + 1) / 234 - (Real.log ((6 * K : ℕ) - 6 : ℝ) + 1) / ((6 * K : ℕ) - 6 : ℝ)) / 3 := by
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ K hK ih =>
    have e : 6 * (K + 1) = 6 * K + 1 + 1 + 1 + 1 + 1 + 1 := by ring
    have c0 : ¬ ((6 * K) % 6 = 1 ∨ (6 * K) % 6 = 5) := by omega
    have c1 : ((6 * K + 1) % 6 = 1 ∨ (6 * K + 1) % 6 = 5) := by omega
    have c2 : ¬ ((6 * K + 1 + 1) % 6 = 1 ∨ (6 * K + 1 + 1) % 6 = 5) := by omega
    have c3 : ¬ ((6 * K + 1 + 1 + 1) % 6 = 1 ∨ (6 * K + 1 + 1 + 1) % 6 = 5) := by omega
    have c4 : ¬ ((6 * K + 1 + 1 + 1 + 1) % 6 = 1 ∨ (6 * K + 1 + 1 + 1 + 1) % 6 = 5) := by omega
    have c5 : ((6 * K + 1 + 1 + 1 + 1 + 1) % 6 = 1 ∨ (6 * K + 1 + 1 + 1 + 1 + 1) % 6 = 5) := by omega
    have hsum : ∑ n ∈ Finset.Ico 240 (6 * (K + 1)),
        (if n % 6 = 1 ∨ n % 6 = 5 then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) =
        ∑ n ∈ Finset.Ico 240 (6 * K),
          (if n % 6 = 1 ∨ n % 6 = 5 then Real.log (n : ℝ) / (n : ℝ) ^ 2 else 0) +
        Real.log ((6 * K + 1 : ℕ) : ℝ) / ((6 * K + 1 : ℕ) : ℝ) ^ 2 +
        Real.log ((6 * K + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) / ((6 * K + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) ^ 2 := by
      rw [e, Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega),
        Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega),
        Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega),
        if_neg c0, if_pos c1, if_neg c2, if_neg c3, if_neg c4, if_pos c5]
      ring
    rw [hsum]
    have hKr : (240 : ℝ) ≤ ((6 * K : ℕ) : ℝ) := by exact_mod_cast (by omega : 240 ≤ 6 * K)
    have a1 := anti ((6 * K : ℕ) : ℝ) ((6 * K + 1 : ℕ) : ℝ) (by linarith) (by push_cast; linarith)
    have a5 := anti ((6 * K : ℕ) : ℝ) ((6 * K + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) (by linarith)
      (by push_cast; linarith)
    have hl : 2 ≤ Real.log ((6 * K : ℕ) : ℝ) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith [exp_two_le]
    have t := tele ((6 * K : ℕ) : ℝ) 6 (by norm_num) (by linarith) hl
    have e2 : (((6 * (K + 1) : ℕ) : ℝ) - 6) = ((6 * K : ℕ) : ℝ) := by push_cast; ring
    rw [e2]
    linarith
end Formalism.DivisionValues.W5
