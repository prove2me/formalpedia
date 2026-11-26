-- Prove2me | solution 1 for FixedOrderFactor.prod_pow_factorization_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:32.632382+00:00
-- url     : https://prove2.me/submissions/8a5c7b25-718c-47c7-8c28-19bef100e17d

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Pairs
public import Definitions.Def_FixedOrderFactor_ModelPairs

set_option autoImplicit true
@[expose] public section
public section
open Finset Complex
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {S : Finset Nat.Primes} {m : ℕ} (hm : 0 < m)
    (hS : ∀ q : Nat.Primes, (q : ℕ) ∣ m → q ∈ S) :
    ∏ q ∈ S, ((q : ℕ) : ℚ) ^ (m.factorization q) = m := by
  have hinj : Function.Injective (fun q : Nat.Primes => (q : ℕ)) := Nat.Primes.coe_nat_injective
  have e : ∏ q ∈ S, ((q : ℕ) : ℚ) ^ (m.factorization q) =
      ∏ p ∈ S.map ⟨_, hinj⟩, (p : ℚ) ^ m.factorization p :=
    (Finset.prod_map S ⟨_, hinj⟩ (fun p : ℕ => (p : ℚ) ^ m.factorization p)).symm
  rw [e]
  have hsub : m.primeFactors ⊆ S.map ⟨_, hinj⟩ := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [Finset.mem_map]
    exact ⟨⟨p, hpp⟩, hS ⟨p, hpp⟩ (Nat.dvd_of_mem_primeFactors hp), rfl⟩
  rw [← Finset.prod_subset hsub]
  · have := Nat.prod_factorization_pow_eq_self hm.ne'
    rw [Finsupp.prod, Nat.support_factorization] at this
    exact_mod_cast this
  · intro p hpS hp
    have hpp : p.Prime := by
      obtain ⟨q, -, rfl⟩ := Finset.mem_map.mp hpS
      exact q.2
    rw [Nat.factorization_eq_zero_of_not_dvd, pow_zero]
    intro hdvd
    exact hp (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, hm.ne'⟩)
end FixedOrderFactor
