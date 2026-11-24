-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_fiber_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:08.622701+00:00
-- url     : https://prove2.me/submissions/bfc83836-51dd-4274-ab46-310f06f8979e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound

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
theorem _root_.solution (N p : ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∑ n ∈ (primesLeFinset N).filter (fun n => n.minFac = p), f n ≤ ∑ a ∈ Icc 1 N, f (p ^ a) := by
  by_cases hp : p.Prime
  · calc ∑ n ∈ (primesLeFinset N).filter (fun n => n.minFac = p), f n
        ≤ ∑ n ∈ (Icc 1 N).image (fun a => p ^ a), f n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [primesLeFinset, mem_filter, mem_Icc] at hn
            obtain ⟨⟨⟨h1, hN⟩, hpp⟩, hmf⟩ := hn
            have e := hpp.minFac_pow_factorization_eq
            rw [hmf] at e
            rw [mem_image]
            refine ⟨n.factorization p, ?_, e⟩
            rw [mem_Icc]
            constructor
            · rcases Nat.eq_zero_or_pos (n.factorization p) with h0 | h0
              · rw [h0, pow_zero] at e
                exact absurd e.symm hpp.ne_one
              · exact h0
            · have : n.factorization p < p ^ n.factorization p := Nat.lt_pow_self hp.one_lt
              omega
          · intro n _ _; exact hf n
      _ = ∑ a ∈ Icc 1 N, f (p ^ a) := by
          apply Finset.sum_image
          intro a _ b _ hab
          exact Nat.pow_right_injective hp.two_le hab
  · have : (primesLeFinset N).filter (fun n => n.minFac = p) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro n hn hmf
      simp only [primesLeFinset, mem_filter] at hn
      exact hp (hmf ▸ Nat.minFac_prime hn.2.ne_one)
    rw [this, Finset.sum_empty]
    exact Finset.sum_nonneg (fun _ _ => hf _)
end Formalism.HermitianLattices.GL2PrimeSums
