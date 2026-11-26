-- Prove2me | solution 1 for FixedOrderFactor.hasProd_zetaN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:15.46708+00:00
-- url     : https://prove2.me/submissions/76469e87-8f37-4e9a-b2f7-a99fc243d9f8

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
public import Theorems.Thm_FixedOrderFactor_summable_fN
public import Theorems.Thm_FixedOrderFactor_zetaN_eq_tsum_fN

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    HasProd (fun q : {q : Nat.Primes // q ∉ N} => (1 - (1 / (q : ℝ)) ^ s)⁻¹) (zetaN N s) := by
  have h := EulerProduct.eulerProduct_completely_multiplicative_hasProd (summable_fN N hs)
  rw [← zetaN_eq_tsum_fN] at h
  have hsupp : Function.mulSupport (fun p : Nat.Primes => (1 - fN N s (by omega) p)⁻¹) ⊆
      {q | q ∉ N} := by
    intro q hq
    simp only [Set.mem_ofPred_eq]
    intro hqN
    apply hq
    show (1 - (if PrimeTo N q then 1 / ((q : ℕ) : ℝ) ^ s else 0))⁻¹ = 1
    rw [if_neg (fun h => h q hqN dvd_rfl)]; simp
  have h2 : HasProd (fun q : {q : Nat.Primes // q ∉ N} => (1 - fN N s (by omega) q.1)⁻¹)
      (zetaN N s) := (hasProd_subtype_iff_of_mulSupport_subset hsupp).mpr h
  convert h2 using 1
  funext q
  show _ = (1 - (if PrimeTo N q.1 then 1 / ((q.1 : ℕ) : ℝ) ^ s else 0))⁻¹
  rw [if_pos]
  · simp [one_div, inv_pow]
  · intro p hp hdvd
    have := (Nat.prime_dvd_prime_iff_eq p.prop q.1.prop).mp hdvd
    exact q.2 (by rwa [← Subtype.ext this])
end FixedOrderFactor
