-- Prove2me | solution 1 for FixedOrderFactor.pow_iff_dvd_valuations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:31.595275+00:00
-- url     : https://prove2.me/submissions/ae9359ac-93fa-4199-b439-233b42cfda26

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Pairs
public import Definitions.Def_FixedOrderFactor_ModelPairs
public import Theorems.Thm_FixedOrderFactor_prod_pow_factorization_eq
public import Theorems.Thm_P2M_FixedOrderFactor_div_eq_pow_iff__ec46a24d60be


set_option autoImplicit true
@[expose] public section
public section
open Finset Complex
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {r : ℕ} (hr : 0 < r) {S : Finset Nat.Primes} {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hS : ∀ q : Nat.Primes, (q : ℕ) ∣ m * n → q ∈ S) :
    (∃ x : ℚ, (m : ℚ) / n = x ^ r) ↔
      ∀ q ∈ S, (r : ℤ) ∣ (m.factorization q : ℤ) - n.factorization q := by
  constructor
  · intro h q _
    obtain ⟨d, a, b, ha, hb, -, rfl, rfl⟩ := (div_eq_pow_iff' hr hm hn).mp h
    have hd : d ≠ 0 := by rintro rfl; simp at hm
    rw [Nat.factorization_mul hd (pow_ne_zero _ ha.ne'),
      Nat.factorization_mul hd (pow_ne_zero _ hb.ne'), Nat.factorization_pow,
      Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact ⟨(a.factorization q : ℤ) - b.factorization q, by push_cast; ring⟩
  · intro h
    refine ⟨∏ q ∈ S, ((q : ℕ) : ℚ) ^
      (((m.factorization q : ℤ) - n.factorization q) / r), ?_⟩
    rw [← Finset.prod_pow]
    have hq : ∀ q ∈ S, (((q : ℕ) : ℚ) ^ (((m.factorization q : ℤ) - n.factorization q) / r)) ^ r
        = ((q : ℕ) : ℚ) ^ (m.factorization q) / ((q : ℕ) : ℚ) ^ (n.factorization q) := by
      intro q hqS
      have hq0 : ((q : ℕ) : ℚ) ≠ 0 := by exact_mod_cast q.2.ne_zero
      rw [← zpow_natCast, ← zpow_mul, Int.ediv_mul_cancel (h q hqS), zpow_sub₀ hq0,
        zpow_natCast, zpow_natCast]
    rw [Finset.prod_congr rfl hq, Finset.prod_div_distrib,
      prod_pow_factorization_eq hm (fun q hq => hS q (hq.mul_right n)),
      prod_pow_factorization_eq hn (fun q hq => hS q (hq.mul_left m))]
end FixedOrderFactor
