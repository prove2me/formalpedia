-- Prove2me | solution 1 for Erdos287.lcm_contains_all_but_one_small_coprime_modulus
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T08:47:00.80866+00:00
-- url     : https://prove2.me/submissions/0bbfc431-5730-4574-ab32-c336831ce8e0

import Mathlib

open Finset

set_option autoImplicit false

private theorem complement_remainder (m base : ℕ) (hm : 0 < m) :
    base + (m - base % m) ≡ 0 [MOD m] := by
  apply Nat.modEq_zero_iff_dvd.mpr
  refine ⟨base / m + 1, ?_⟩
  rw [Nat.mul_add, Nat.mul_one]
  have hdiv := Nat.mod_add_div base m
  have hrem := Nat.mod_lt base hm
  omega

/-- A set hitting every consecutive pair cannot miss two coprime divisibility
classes whose joint period fits within the interval. -/
theorem solution (D : Finset ℕ) (lo hi : ℕ)
    (hcover : ∀ x, lo ≤ x → x + 1 ≤ hi → x ∈ D ∨ x + 1 ∈ D) :
    (∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a * b ≤ hi - lo →
      a ∣ D.lcm id ∨ b ∣ D.lcm id) ∧
    (∀ (P : Finset ℕ) (K : ℕ), K * K ≤ hi - lo →
      (∀ a ∈ P, 0 < a ∧ a ≤ K) →
      (∀ a ∈ P, ∀ b ∈ P, a ≠ b → Nat.Coprime a b) →
      (P.filter fun a => ¬ a ∣ D.lcm id).card ≤ 1) := by
  have hpair (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : Nat.Coprime a b)
      (hwidth : a * b ≤ hi - lo) : a ∣ D.lcm id ∨ b ∣ D.lcm id := by
    let ca := a - lo % a
    let cb := b - (lo + 1) % b
    let c := Nat.chineseRemainder hc ca cb
    have hc₀ : (c : ℕ) < a * b := Nat.chineseRemainder_lt_mul hc ca cb ha.ne' hb.ne'
    let x := lo + (c : ℕ)
    have hxlo : lo ≤ x := by dsimp [x]; omega
    have hxhi : x + 1 ≤ hi := by
      have hp : 0 < a * b := Nat.mul_pos ha hb
      dsimp [x]
      omega
    have hxa : a ∣ x := by
      apply Nat.modEq_zero_iff_dvd.mp
      exact ((Nat.ModEq.refl lo).add c.property.1).trans (complement_remainder a lo ha)
    have hxb : b ∣ x + 1 := by
      have hmod : lo + 1 + (c : ℕ) ≡ 0 [MOD b] :=
        ((Nat.ModEq.refl (lo + 1)).add c.property.2).trans (complement_remainder b (lo + 1) hb)
      exact Nat.modEq_zero_iff_dvd.mp (by simpa only [x, add_right_comm lo] using hmod)
    rcases hcover x hxlo hxhi with hx | hy
    · exact Or.inl (hxa.trans (Finset.dvd_lcm hx))
    · exact Or.inr (hxb.trans (Finset.dvd_lcm hy))
  refine ⟨hpair, ?_⟩
  intro P K hwidth hP hcop
  apply Finset.card_le_one_iff.mpr
  intro a b ha hb
  obtain ⟨haP, hna⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbP, hnb⟩ := Finset.mem_filter.mp hb
  by_contra hne
  have hprod : a * b ≤ hi - lo := (Nat.mul_le_mul (hP a haP).2 (hP b hbP).2).trans hwidth
  exact (hpair a b (hP a haP).1 (hP b hbP).1 (hcop a haP b hbP hne) hprod).elim hna hnb

