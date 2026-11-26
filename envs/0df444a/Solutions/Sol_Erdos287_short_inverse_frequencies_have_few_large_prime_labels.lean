-- Prove2me | solution 1 for Erdos287.short_inverse_frequencies_have_few_large_prime_labels
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:04:59.820029+00:00
-- url     : https://prove2.me/submissions/9ebaf07e-0877-4736-bcc0-781c95bd8993

import Mathlib

open Finset

set_option autoImplicit false

/-- Reciprocals in a short arc of a nonzero additive frequency can be
covered by divisors of a short list of integers. Distinct large prime
labels give a uniform bound on the multiplicity of that cover. -/
theorem solution (D : Finset ℕ) (label : ℕ → ℕ) (M q a R Y K : ℕ)
    (ha : 0 < a) (haq : a < q) (hY : 2 ≤ Y)
    (hD : ∀ n ∈ D, n ≤ M ∧ (label n).Prime ∧ Y ≤ label n ∧ label n ∣ n)
    (hinj : Set.InjOn label (↑D : Set ℕ))
    (hphase : ∀ n ∈ D, ∃ r ≤ R, n * r ≡ a [MOD q] ∨ n * r ≡ q - a [MOD q])
    (hsize : (M * R / q + 1) * q < Y ^ (K + 1)) :
    D.card ≤ 2 * (M * R / q + 1) * K := by
  classical
  let J := range (M * R / q + 1)
  let V := J.image (fun j => a + j * q) ∪ J.image (fun j => q - a + j * q)
  let F (v : ℕ) := D.filter (fun n => label n ∣ v)
  have hV (v : ℕ) (hv : v ∈ V) : 0 < v ∧ v < Y ^ (K + 1) := by
    have hworker (b : ℕ) (hb : 0 < b) (hbq : b < q) (j : ℕ) (hj : j ∈ J) :
        0 < b + j * q ∧ b + j * q < Y ^ (K + 1) := by
      have hj' : j < M * R / q + 1 := mem_range.mp hj
      have hmul := Nat.mul_le_mul_right q (Nat.le_of_lt_succ hj')
      rw [Nat.add_mul, one_mul] at hsize
      constructor
      · omega
      · omega
    rcases mem_union.mp hv with h | h
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp h
      exact hworker a ha haq j hj
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp h
      exact hworker (q - a) (by omega) (by omega) j hj
  have hcover : D ⊆ V.biUnion F := by
    intro n hn
    obtain ⟨r, hr, hmod⟩ := hphase n hn
    let j := n * r / q
    have hj : j ∈ J := by
      apply mem_range.mpr
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.mul_le_mul (hD n hn).1 hr))
    have hreach (b : ℕ) (hb : b < q) (h : n * r ≡ b [MOD q]) : n ∣ b + j * q := by
      have hnmod : n * r % q = b := Eq.trans h (Nat.mod_eq_of_lt hb)
      have he : b + j * q = n * r := by
        simpa only [j, hnmod, mul_comm q] using Nat.mod_add_div (n * r) q
      rw [he]
      exact dvd_mul_right n r
    have hc (v : ℕ) (hv : v ∈ V) (hd : n ∣ v) : n ∈ V.biUnion F :=
      mem_biUnion.mpr ⟨v, hv, mem_filter.mpr ⟨hn, (hD n hn).2.2.2.trans hd⟩⟩
    rcases hmod with h | h
    · exact hc (a + j * q) (mem_union_left _ (mem_image_of_mem _ hj)) (hreach a haq h)
    · exact hc (q - a + j * q) (mem_union_right _ (mem_image_of_mem _ hj))
        (hreach (q - a) (by omega) h)
  have hcount (v : ℕ) (hv : v ∈ V) : (F v).card ≤ K := by
    let P := (F v).image label
    have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ Y ≤ p ∧ p ∣ v := by
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hp
      obtain ⟨hnD, hnV⟩ := mem_filter.mp hn
      exact ⟨(hD n hnD).2.1, (hD n hnD).2.2.1, hnV⟩
    have hprod : (∏ p ∈ P, p) ∣ v := by
      apply Int.natCast_dvd_natCast.mp
      rw [Nat.cast_prod]
      refine Finset.prod_dvd_of_coprime ?_ (fun p hp => Int.natCast_dvd_natCast.mpr (hP p hp).2.2)
      intro p hp r hr hpr
      exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hP p hp).1 (hP r hr).1).mpr hpr)
    have hlow : Y ^ P.card ≤ ∏ p ∈ P, p := pow_card_le_prod _ _ _ fun p hp => (hP p hp).2.1
    have hlt : Y ^ P.card < Y ^ (K + 1) := hlow.trans_lt
      ((Nat.le_of_dvd (hV v hv).1 hprod).trans_lt (hV v hv).2)
    have hcard : P.card = (F v).card := by
      apply card_image_of_injOn
      intro a ha b hb he
      exact hinj (mem_filter.mp ha).1 (mem_filter.mp hb).1 he
    rw [← hcard]
    exact Nat.lt_succ_iff.mp ((pow_lt_pow_iff_right₀ (show 1 < Y by omega)).mp hlt)
  have hcardV : V.card ≤ 2 * (M * R / q + 1) := calc
    _ ≤ (J.image (fun j => a + j * q)).card + (J.image (fun j => q - a + j * q)).card :=
      card_union_le _ _
    _ ≤ J.card + J.card := add_le_add card_image_le card_image_le
    _ = _ := by simp [J, two_mul]
  calc
    D.card ≤ (V.biUnion F).card := card_le_card hcover
    _ ≤ ∑ v ∈ V, (F v).card := card_biUnion_le
    _ ≤ ∑ _ ∈ V, K := sum_le_sum hcount
    _ = V.card * K := by simp
    _ ≤ _ := Nat.mul_le_mul_right K hcardV

