-- Prove2me | solution 1 for CyclotomicEulerSystem.exists_compatibleRootSystem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T12:51:26.608071+00:00
-- url     : https://prove2.me/submissions/b5021513-2ab1-42c2-b0d6-c981532eed59

import Definitions.Def_CyclotomicEulerSystem_defs

open scoped BigOperators
open CyclotomicEulerSystem

private lemma primitive_prime_product (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    IsPrimitiveRoot (∏ p ∈ s, Complex.exp (2 * Real.pi * Complex.I / p)) (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hprime := hs p (Finset.mem_insert_self p s)
    have htail := ih (fun q hq => hs q (Finset.mem_insert_of_mem hq))
    have hroot := Complex.isPrimitiveRoot_exp p hprime.ne_zero
    have hcop : p.Coprime (∏ q ∈ s, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact (Nat.coprime_primes hprime (hs q (Finset.mem_insert_of_mem hq))).mpr
        (fun heq => hp (heq ▸ hq))
    rw [Finset.prod_insert hp, Finset.prod_insert hp, IsPrimitiveRoot.iff_orderOf]
    rw [(Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime
      (by simpa [← hroot.eq_orderOf, ← htail.eq_orderOf] using hcop)]
    rw [← hroot.eq_orderOf, ← htail.eq_orderOf]

theorem solution : ∃ ζ : ℕ → ℂ, IsCompatibleRootSystem ζ := by
  classical
  refine ⟨fun n => ∏ p ∈ n.primeFactors, Complex.exp (2 * Real.pi * Complex.I / p), ?_, ?_⟩
  · intro n hn
    simpa only [Nat.prod_primeFactors_of_squarefree hn] using
      primitive_prime_product n.primeFactors (fun p hp => (Nat.mem_primeFactors.mp hp).1)
  · intro m n _ _ hcop
    exact congrArg (fun s : Finset ℕ => ∏ p ∈ s,
      Complex.exp (2 * Real.pi * Complex.I / p)) hcop.primeFactors_mul |>.trans
        (Finset.prod_union hcop.disjoint_primeFactors)
