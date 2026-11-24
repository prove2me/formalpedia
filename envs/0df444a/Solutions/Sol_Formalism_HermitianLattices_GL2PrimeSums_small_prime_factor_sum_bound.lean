-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.small_prime_factor_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:53.598798+00:00
-- url     : https://prove2.me/submissions/f7bbf217-8a2e-4a72-8321-cf7b52993408

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_cn_nonneg
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_le_log
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_count
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_minFac_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums
namespace Formalism.HermitianLattices.GL2PrimeSums
theorem _root_.solution {x : ℝ} (hx : Real.exp 1 ≤ x) (N m₀ : ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (h : ∀ p : ℕ, p.Prime → p ∣ m₀ → p ≤ N → (p : ℝ) ≤ Y) :
    ∑ n ∈ (primesLeFinset N).filter (fun n => n.minFac ∣ m₀), cn x n ≤ Y * (3 * Real.log x) := by
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun n hn => gl2a5_minFac_mem (N := N) (mem_filter.1 hn).1)]
  have hpt : ∀ p ∈ Icc 1 N, ∑ n ∈ ((primesLeFinset N).filter (fun n => n.minFac ∣ m₀)).filter
      (fun n => n.minFac = p), cn x n ≤ (if (p : ℝ) ≤ Y then (1 : ℝ) else 0) * (3 * Real.log x) := by
    intro p hpN
    by_cases hp : p.Prime ∧ p ∣ m₀
    · rw [if_pos (h p hp.1 hp.2 (mem_Icc.1 hpN).2), one_mul]
      refine le_trans ?_ (gl2a5s_le_log hx N p)
      unfold primeTermWeight
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        simp only [mem_filter] at hn ⊢
        exact ⟨hn.1.1, hn.2⟩
      · intro n _ _; exact gl2a5_cn_nonneg (by linarith) n
    · have : ((primesLeFinset N).filter (fun n => n.minFac ∣ m₀)).filter (fun n => n.minFac = p) = ∅ := by
        apply Finset.filter_eq_empty_iff.2
        intro n hn hmf
        simp only [primesLeFinset, mem_filter] at hn
        exact hp ⟨hmf ▸ Nat.minFac_prime hn.1.2.ne_one, hmf ▸ hn.2⟩
      rw [this, Finset.sum_empty]
      split_ifs <;> positivity
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (gl2a5_count N Y hY) (by positivity)
end Formalism.HermitianLattices.GL2PrimeSums
