-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.centralBinom_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:58.214192+00:00
-- url     : https://prove2.me/submissions/d9b488ad-48b9-4af2-9534-2ade06912ec8

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Nat
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
theorem _root_.solution (n : ℕ) (n_large : 2 < n) :
    centralBinom n ≤
      ((2 * n) ^ (primeCounting (sqrt (2 * n))) * 4 ^ (2 * n / 3)) * (2 * n) ^ (upper n).card := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 ≤ 2 * n := mul_pos (zero_lt_two' ℕ) n_pos
  let S0 := {p ∈ Finset.range (2 * n + 1) | Nat.Prime p}
  let f x := x ^ n.centralBinom.factorization x
  have hf : ∀ p, f p ≤ 2 * n := fun p => pow_factorization_choose_le (mul_pos two_pos n_pos)
  have h0 : ∏ x ∈ S0, f x = centralBinom n := by
    rw [← n.prod_pow_factorization_centralBinom]
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose h; dsimp only [f]
    rw [factorization_eq_zero_of_not_prime n.centralBinom h, _root_.pow_zero]
  rw [← h0, ← Finset.prod_filter_mul_prod_filter_not S0 (· ≤ 2 * n / 3)]
  apply mul_le_mul'
  · rw [← Finset.prod_filter_mul_prod_filter_not _ (· ≤ sqrt (2 * n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod' fun p _ => hf p).trans ?_
      rw [Finset.prod_const]
      refine pow_right_mono₀ n2_pos ?_
      rw [← primesLE_card_eq_primeCounting]
      refine Finset.card_le_card fun x hx => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      obtain ⟨h3, _⟩ := Finset.mem_filter.1 h1
      exact mem_primesLE.mpr ⟨h2, (Finset.mem_filter.1 h3).2⟩
    · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
      refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        obtain ⟨h3, _⟩ := Finset.mem_filter.1 h1
        refine (pow_right_mono₀ (Finset.mem_filter.1 h3).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
      · unfold primorial
        refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
        · intro p hp
          obtain ⟨h1, _⟩ := Finset.mem_filter.1 hp
          obtain ⟨h3, h4⟩ := Finset.mem_filter.1 h1
          exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), (Finset.mem_filter.1 h3).2⟩
        · exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  · rw [← Finset.prod_filter_mul_prod_filter_not _ (· ≤ n)]
    have h1 : ∏ x ∈ {x ∈ {x ∈ S0 | ¬ x ≤ 2 * n / 3} | x ≤ n}, f x = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      obtain ⟨_, h4⟩ := Finset.mem_filter.1 h1
      dsimp only [f]
      rw [factorization_centralBinom_of_two_mul_self_lt_three_mul n_large h2 (by omega),
        _root_.pow_zero]
    rw [h1, one_mul]
    refine (Finset.prod_le_prod' fun p _ => hf p).trans ?_
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos (Finset.card_le_card fun x hx => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    obtain ⟨h3, _⟩ := Finset.mem_filter.1 h1
    obtain ⟨h5, h6⟩ := Finset.mem_filter.1 h3
    exact Finset.mem_filter.2 ⟨h5, h6, by omega⟩
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
