-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.sum_vonMangoldt_primePow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:06.036406+00:00
-- url     : https://prove2.me/submissions/d5f867fb-a17c-436e-8f3b-f87c3b4e13d5

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
open PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData
theorem _root_.solution (N : ℕ) (X : ℕ → ℂ)
    (hX : ∀ p i, p.Prime → 1 ≤ i → N < p ^ i → X (p ^ i) = 0) :
    ∑ n ∈ Icc 1 N, (Λ n : ℂ) * X n
      = ∑ p ∈ (range (N + 1)).filter Nat.Prime, ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * X (p ^ i) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.1 ^ x.2) ?_ ?_ ?_ ?_
  · intro x hx hne
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hx
    obtain ⟨⟨_, hp⟩, hi1, _⟩ := hx
    have hle : x.1 ^ x.2 ≤ N := by
      by_contra hlt
      exact hne (by rw [hX x.1 x.2 hp hi1 (not_le.1 hlt), mul_zero])
    show x.1 ^ x.2 ∈ Icc 1 N
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_pow _ _ hp.pos, hle⟩
  · intro x hx _ y hy _ hxy
    have hxy' : x.1 ^ x.2 = y.1 ^ y.2 := hxy
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hx hy
    obtain ⟨⟨_, hp⟩, hi1, _⟩ := hx
    obtain ⟨⟨_, hq⟩, hj1, _⟩ := hy
    have hpq : x.1 = y.1 := by
      have hd : x.1 ∣ y.1 ^ y.2 := by
        rw [← hxy']
        exact dvd_pow_self _ (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hd)
    have hij : x.2 = y.2 := by
      rw [hpq] at hxy'
      exact Nat.pow_right_injective hq.two_le hxy'
    exact Prod.ext hpq hij
  · intro n hn hne
    rw [Finset.mem_Icc] at hn
    have hΛ : Λ n ≠ 0 := by
      intro h0
      apply hne
      show (Λ n : ℂ) * X n = 0
      rw [h0]
      simp
    rw [ArithmeticFunction.vonMangoldt_ne_zero_iff, isPrimePow_nat_iff] at hΛ
    obtain ⟨p, k, hp, hk, rfl⟩ := hΛ
    have h1 : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    have h2 : k < p ^ k := by
      first
      | exact Nat.lt_pow_self hp.one_lt
      | exact Nat.lt_pow_self hp.one_lt k
    refine ⟨(p, k), ?_, ?_, rfl⟩
    · rw [Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      exact ⟨⟨Nat.lt_succ_of_le (h1.trans hn.2), hp⟩, hk, (h2.trans_le hn.2).le⟩
    · intro h0
      apply hne
      show (Λ (p ^ k) : ℂ) * X (p ^ k) = 0
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime hp]
      exact h0
  · intro x hx _
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hx
    show (Real.log x.1 : ℂ) * X (x.1 ^ x.2) = (Λ (x.1 ^ x.2) : ℂ) * X (x.1 ^ x.2)
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hx.1.2]
end Formalism.LFunctionChainParameters.characterSumData
