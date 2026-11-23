-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5_abel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:34.01083+00:00
-- url     : https://prove2.me/submissions/6a975a42-dd32-4a03-91d6-dc2ff6b97d1a

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
theorem _root_.solution (hψ : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (g : ℕ → ℝ) (K : ℕ)
    (hanti : ∀ n, K < n → g (n + 1) ≤ g n) (hnn : ∀ n, K < n → 0 ≤ g n) (M : ℕ) :
    ∑ n ∈ Ioc K M, Λ n * g n ≤ 2 * ((K : ℝ) + 1) * g (K + 1) + 2 * ∑ n ∈ Ioc (K + 1) M, g n := by
  have hsub : ∀ M : ℕ, ∑ n ∈ Ioc K M, Λ n ≤ 2 * (M : ℝ) := by
    intro M
    refine le_trans ?_ (hψ M)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [mem_Ioc, mem_Icc] at hn ⊢
      omega
    · intro _ _ _; exact vonMangoldt_nonneg
  rcases Nat.lt_or_ge K M with hKM | hKM
  · have key : ∀ M, K + 1 ≤ M → g M * (2 * (M : ℝ) - ∑ n ∈ Ioc K M, Λ n) ≤
        2 * ((K : ℝ) + 1) * g (K + 1) + 2 * ∑ n ∈ Ioc (K + 1) M, g n - ∑ n ∈ Ioc K M, Λ n * g n := by
      intro M hM
      induction M, hM using Nat.le_induction with
      | base =>
        rw [Finset.sum_Ioc_succ_top le_rfl, Finset.sum_Ioc_succ_top le_rfl]
        simp only [Finset.Ioc_self, Finset.sum_empty]
        push_cast
        apply le_of_eq; ring
      | succ M hM ih =>
        rw [Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega),
          Finset.sum_Ioc_succ_top (by omega)]
        have h1 := hanti M (by omega)
        have h2 := hsub M
        have h3 : g (M + 1) * (2 * (M : ℝ) - ∑ n ∈ Ioc K M, Λ n) ≤
            g M * (2 * (M : ℝ) - ∑ n ∈ Ioc K M, Λ n) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
        push_cast
        nlinarith [h3, ih]
    have h1 := key M hKM
    have h2 : 0 ≤ g M * (2 * (M : ℝ) - ∑ n ∈ Ioc K M, Λ n) :=
      mul_nonneg (hnn M hKM) (by linarith [hsub M])
    linarith
  · rw [Finset.Ioc_eq_empty (by omega), Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty, mul_zero, add_zero]
    have := hnn (K + 1) (by omega)
    positivity
end Formalism.HermitianLattices.GL2PrimeSums
