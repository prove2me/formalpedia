-- Prove2me | solution 1 for Erdos287.cofactor_subsum_count_from_prime_factorization_of_lcm
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T07:36:46.671393+00:00
-- url     : https://prove2.me/submissions/c81afd58-a72b-45ee-a565-f0fde0bb90a4

import Mathlib
import Theorems.Thm_Erdos287_cofactor_subset_sums_compress_by_coprime_residues

open Finset

set_option autoImplicit false

/-- For a large prime factor of the cofactor LCM its residue only sees
cofactors divisible by that prime. -/
theorem solution (B Z : ℕ) :
    let U := Finset.Icc 1 B
    let L := U.lcm id
    ∃ F : Finset (Finset ℕ),
      (∀ T ∈ F, T ⊆ U ∧ T.Nonempty) ∧
      (∀ T ⊆ U, T.Nonempty → ∃ V ∈ F, (∑ x ∈ V, L / x) = ∑ x ∈ T, L / x) ∧
      F.card ≤ (B + 1) * ∏ p ∈ L.primeFactors,
        if p ≤ Z then p ^ L.factorization p else 2 ^ (B / p) := by
  classical
  dsimp only
  let U := Icc 1 B
  let L := U.lcm id
  let q (p : ℕ) := p ^ L.factorization p
  let w (x : ℕ) := L / x
  change ∃ F : Finset (Finset ℕ),
    (∀ T ∈ F, T ⊆ U ∧ T.Nonempty) ∧
    (∀ T ⊆ U, T.Nonempty → ∃ V ∈ F, (∑ x ∈ V, w x) = ∑ x ∈ T, w x) ∧
    F.card ≤ (B + 1) * ∏ p ∈ L.primeFactors, if p ≤ Z then q p else 2 ^ (B / p)
  have hL0 : L ≠ 0 := by
    apply Finset.lcm_ne_zero_iff.mpr
    intro n hn
    change n ≠ 0
    exact Nat.ne_of_gt (mem_Icc.mp hn).1
  have hprod : L = ∏ p ∈ L.primeFactors, q p := Nat.prod_primeFactors_pow_factorization hL0
  have hprime (p : ℕ) (hp : p ∈ L.primeFactors) : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hcop (p : ℕ) (hp : p ∈ L.primeFactors) (r : ℕ) (hr : r ∈ L.primeFactors)
      (hne : p ≠ r) : (q p).Coprime (q r) :=
    Nat.coprime_pow_primes _ _ (hprime p hp) (hprime r hr) hne
  obtain ⟨F, hFU, hrepr, hbound⟩ :=
    Erdos287.cofactor_subset_sums_compress_by_coprime_residues U L.primeFactors q w L
      hprod (fun p hp => pow_pos (hprime p hp).pos _) hcop (fun x _ => Nat.div_le_self _ x)
  refine ⟨F, hFU, hrepr, hbound.trans ?_⟩
  have hcardU : U.card = B := by simp [U]
  rw [hcardU]
  refine Nat.mul_le_mul_left _ (prod_le_prod' fun p hp => ?_)
  by_cases hpZ : p ≤ Z
  · rw [if_pos hpZ]
    exact min_le_left _ _
  · have hqL : q p ∣ L := by
      rw [hprod]
      exact Finset.dvd_prod_of_mem q hp
    let S := U.filter (fun x => ¬ q p ∣ w x)
    have hdvd (x : ℕ) (hx : x ∈ S) : p ∣ x := by
      obtain ⟨hxU, hxND⟩ := mem_filter.mp hx
      by_contra hpN
      have hqr : (q p).Coprime x := ((hprime p hp).coprime_iff_not_dvd.mpr hpN).pow_left _
      have heq : w x * x = L := Nat.div_mul_cancel (Finset.dvd_lcm hxU)
      have hdiv := hqr.dvd_of_dvd_mul_right (heq.symm ▸ hqL)
      exact hxND hdiv
    have hsize : S.card ≤ B / p := by
      have hmap : Set.MapsTo (fun x : ℕ => x / p) (↑S : Set ℕ)
          (↑(Icc 1 (B / p)) : Set ℕ) := by
        intro x hx
        obtain hxu := mem_Icc.mp (mem_filter.mp hx).1
        exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hxu.1 (hdvd x hx)) (hprime p hp).pos,
          Nat.div_le_div_right hxu.2⟩
      have hinj : Set.InjOn (fun x : ℕ => x / p) (↑S : Set ℕ) := by
        intro x hx y hy he
        change x / p = y / p at he
        calc
          x = (x / p) * p := (Nat.div_mul_cancel (hdvd x hx)).symm
          _ = (y / p) * p := by rw [he]
          _ = y := Nat.div_mul_cancel (hdvd y hy)
      simpa using card_le_card_of_injOn (fun x : ℕ => x / p) hmap hinj
    have hpow : (2 : ℕ) ^ S.card ≤ 2 ^ (B / p) := by gcongr <;> decide
    simpa [hpZ, S] using (min_le_right (q p) (2 ^ S.card)).trans hpow

