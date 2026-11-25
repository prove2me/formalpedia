-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.q_p_threshold_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:22:32.723937+00:00
-- url     : https://prove2.me/submissions/1bae24b1-a694-4a8f-9a5a-9b4984be750e

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_PropositionOneCentralCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartEqIff
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRTypeCountExact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : QPThreshold := by
  intro c d Q m X N hc hd1 hdc hQ0 hQc hm0 hmc hN hX hmain
  have hc1 : (1 : ℝ) ≤ c := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hd0 : (0 : ℝ) ≤ d := by linarith
  have hA : c ^ 500 ≤ (X * c ^ (-20 : ℤ)) ^ ((1 : ℝ) / 4) := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hN)
    calc c ^ 500 = 1 * c ^ 500 := (one_mul _).symm
      _ ≤ (N : ℝ) ^ 4 * c ^ 500 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ _ := hmain
  have hXc : 0 ≤ X * c ^ (-20 : ℤ) := mul_nonneg hX.le (zpow_nonneg hc0.le _)
  have hB : c ^ 2000 ≤ X * c ^ (-20 : ℤ) := by
    have h4 := pow_le_pow_left₀ (by positivity) hA 4
    have e1 : ((X * c ^ (-20 : ℤ)) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = X * c ^ (-20 : ℤ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hXc]
      norm_num
    rw [e1, ← pow_mul] at h4
    exact h4
  have hC : c ^ 2020 ≤ X := by
    have e2 : X * c ^ (-20 : ℤ) * c ^ (20 : ℕ) = X := by
      rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hc0.ne']
      norm_num
    calc c ^ 2020 = c ^ 2000 * c ^ 20 := by ring
      _ ≤ X * c ^ (-20 : ℤ) * c ^ 20 := mul_le_mul_of_nonneg_right hB (by positivity)
      _ = X := e2
  have t1 : d ^ 694 * Q ^ 521 ≤ c ^ 1736 := by
    have a1 : d ^ 694 ≤ c ^ 694 := pow_le_pow_left₀ hd0 hdc _
    have a2 : Q ^ 521 ≤ (c ^ 2) ^ 521 := pow_le_pow_left₀ hQ0 hQc _
    calc d ^ 694 * Q ^ 521 ≤ c ^ 694 * (c ^ 2) ^ 521 :=
          mul_le_mul a1 a2 (pow_nonneg hQ0 _) (by positivity)
      _ = c ^ 1736 := by ring
  have t2 : d ^ 232 * Q ^ 367 * (2 : ℝ) ^ (290 * 2) ≤ c ^ 1256 := by
    have a1 : d ^ 232 ≤ c ^ 232 := pow_le_pow_left₀ hd0 hdc _
    have a2 : Q ^ 367 ≤ (c ^ 2) ^ 367 := pow_le_pow_left₀ hQ0 hQc _
    have a3 : (2 : ℝ) ^ (290 * 2) ≤ c ^ 290 := by
      rw [pow_mul']
      exact pow_le_pow_left₀ (by norm_num) (by norm_num; linarith) _
    calc d ^ 232 * Q ^ 367 * (2 : ℝ) ^ (290 * 2) ≤ c ^ 232 * (c ^ 2) ^ 367 * c ^ 290 :=
          mul_le_mul (mul_le_mul a1 a2 (pow_nonneg hQ0 _) (by positivity)) a3 (by positivity)
            (by positivity)
      _ = c ^ 1256 := by ring
  have t3 : (d * Q * (2 : ℝ) ^ 2) ^ ((1 : ℝ) / 1000) * m ≤ 2 * c ^ 6 := by
    have hb0 : 0 ≤ d * Q * (2 : ℝ) ^ 2 := mul_nonneg (mul_nonneg hd0 hQ0) (by norm_num)
    have hr : (d * Q * (2 : ℝ) ^ 2) ^ ((1 : ℝ) / 1000) ≤ 1 + d * Q * (2 : ℝ) ^ 2 := by
      rcases le_or_gt (d * Q * (2 : ℝ) ^ 2) 1 with h | h
      · have := Real.rpow_le_one hb0 h (by norm_num : (0 : ℝ) ≤ 1 / 1000)
        linarith
      · have := Real.rpow_le_rpow_of_exponent_le h.le (by norm_num : (1 : ℝ) / 1000 ≤ 1)
        rw [Real.rpow_one] at this
        linarith
    have hq : d * Q * (2 : ℝ) ^ 2 ≤ c ^ 4 := by
      have h1 : d * Q ≤ c * c ^ 2 := mul_le_mul hdc hQc hQ0 hc0.le
      nlinarith [mul_nonneg (pow_nonneg hc0.le 3) (by linarith : (0 : ℝ) ≤ c - 4)]
    have h4 : (1 : ℝ) ≤ c ^ 4 := one_le_pow₀ hc1
    calc (d * Q * (2 : ℝ) ^ 2) ^ ((1 : ℝ) / 1000) * m ≤ (1 + c ^ 4) * c ^ 2 :=
          mul_le_mul (by linarith) hmc hm0 (by positivity)
      _ ≤ 2 * c ^ 6 := by nlinarith [mul_le_mul_of_nonneg_left h4 (sq_nonneg c)]
  have f1 : c ^ 1256 ≤ c ^ 1736 := pow_le_pow_right₀ hc1 (by norm_num)
  have f2 : c ^ 6 ≤ c ^ 1736 := pow_le_pow_right₀ hc1 (by norm_num)
  have f3 : 4 * c ^ 1736 ≤ c ^ 2020 := by
    have h5 : (4 : ℝ) ≤ c ^ 284 := le_trans hc (le_self_pow₀ hc1 (by norm_num))
    calc 4 * c ^ 1736 ≤ c ^ 284 * c ^ 1736 := mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = c ^ 2020 := by ring
  have s1 : c ^ 1736 + c ^ 1256 + 2 * c ^ 6 ≤ 4 * c ^ 1736 := by linarith
  exact le_trans (add_le_add (add_le_add t1 t2) t3) (le_trans s1 (le_trans f3 hC))
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
