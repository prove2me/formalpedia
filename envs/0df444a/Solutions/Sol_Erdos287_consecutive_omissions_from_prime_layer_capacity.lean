-- Prove2me | solution 1 for Erdos287.consecutive_omissions_from_prime_layer_capacity
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T07:23:42.881045+00:00
-- url     : https://prove2.me/submissions/5bcfbe9f-fdb6-40e0-be48-a3bfe61f94a3

import Mathlib
import Theorems.Thm_Erdos287_exact_prime_power_in_reduced_denominator
import Theorems.Thm_Erdos287_few_exceptional_primes_for_cofactor_subsets

open Finset

set_option autoImplicit false

/-- Disjoint adjacent pairs with large prime labels cannot all be hit by
denominators if the total capacity of the usable prime layers is too small. -/
theorem solution (D S J : Finset ℕ) (m M : ℕ)
    (P U : ℕ → Finset ℕ) (F : ℕ → Finset (Finset ℕ)) (L Y K : ℕ → ℕ)
    (hD : ∀ n ∈ D, 0 < n ∧ n ≤ M)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hends : ∀ x ∈ S, m ≤ x ∧ x + 1 ≤ M)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + 1 < y ∨ y + 1 < x)
    (hlabels : ∀ x ∈ S, ∀ n : ℕ, (n = x ∨ n = x + 1) →
      ∃ i ∈ J, ∃ p ∈ P i, p ∣ n)
    (hgroups : ∀ i ∈ J, 0 < L i ∧ 2 ≤ Y i ∧
      (∀ b ∈ U i, 0 < b ∧ b ∣ L i) ∧
      (∀ T ∈ F i, T ⊆ U i ∧ T.Nonempty) ∧
      (∀ p ∈ P i, p.Prime ∧ Y i ≤ p ∧ ¬ p ∣ L i) ∧
      (U i).card * L i < Y i ^ (K i + 1))
    (hconfig : ∀ i ∈ J, ∀ p ∈ P i, (∃ n ∈ D, p ∣ n) → ∃ e : ℕ, 1 ≤ e ∧
      (∀ n ∈ D, padicValNat p n ≤ e) ∧
      (∀ n ∈ D, padicValNat p n = e → n / p ^ e ∈ U i) ∧
      ∃ T ∈ F i, (∑ b ∈ T, L i / b) =
        ∑ n ∈ D.filter (fun n => padicValNat p n = e), L i / (n / p ^ e))
    (hmany : (∑ i ∈ J, (M / Y i) * ((F i).card * K i)) < S.card) :
    ∃ x, m ≤ x ∧ x + 1 ≤ M ∧ x ∉ D ∧ x + 1 ∉ D := by
  classical
  by_contra hgap
  let used (i : ℕ) := (P i).filter (fun p => ∃ n ∈ D, p ∣ n)
  let multiples (i p : ℕ) := (Icc 1 (M / Y i)).image (fun b => b * p)
  let candidates (i : ℕ) := (used i).biUnion (multiples i)
  let hit (x : ℕ) := if x ∈ D then x else x + 1
  have hused (i : ℕ) (hi : i ∈ J) : (used i).card ≤ (F i).card * K i := by
    obtain ⟨hL, hY, hU, hF, hP, hbound⟩ := hgroups i hi
    refine Erdos287.few_exceptional_primes_for_cofactor_subsets (U i) (used i) (F i)
      (L i) (Y i) (K i) hL hY hU hF
      (fun p hp => ⟨(hP p (mem_filter.mp hp).1).1, (hP p (mem_filter.mp hp).1).2.1⟩) hbound ?_
    intro p hp
    obtain ⟨hpP, hpD⟩ := mem_filter.mp hp
    obtain ⟨e, he, hmax, hcof, T, hT, heq⟩ := hconfig i hi p hpP hpD
    obtain ⟨hprime, _, hpL⟩ := hP p hpP
    have hcrt := Erdos287.exact_prime_power_in_reduced_denominator D (fun _ => 1) p e (L i)
      hprime he hpL (fun n hn => (hD n hn).1) hmax
      (fun n hn hv => (hU _ (hcof n hn hv)).2)
    refine ⟨T, hT, ?_⟩
    rw [heq]
    by_contra hnot
    have hq := hcrt.mpr (by simpa only [one_mul, ← Nat.cast_sum, Int.natCast_dvd_natCast] using hnot)
    have hzero := padicValNat.eq_zero_of_not_dvd hprime.not_dvd_one
    simp only [Int.cast_one, hsum, Rat.den_one, hzero] at hq
    omega
  have hhit (x : ℕ) (hx : x ∈ S) : hit x ∈ D ∧ (hit x = x ∨ hit x = x + 1) := by
    by_cases h : x ∈ D
    · simp [hit, h]
    · have hn : x + 1 ∈ D := by
        by_contra hnext
        exact hgap ⟨x, (hends x hx).1, (hends x hx).2, h, hnext⟩
      simpa [hit, h] using hn
  have hcover : Set.MapsTo hit (↑S : Set ℕ) (↑(J.biUnion candidates) : Set ℕ) := by
    intro x hx
    obtain ⟨hn, hside⟩ := hhit x hx
    obtain ⟨i, hi, p, hp, hdvd⟩ := hlabels x hx (hit x) hside
    obtain ⟨_, _, _, _, hP, _⟩ := hgroups i hi
    have hpos := (hD _ hn).1
    have hpY := (hP p hp).2.1
    have hp0 := (hP p hp).1.pos
    have hq0 : 0 < hit x / p := Nat.div_pos (Nat.le_of_dvd hpos hdvd) hp0
    have hqb : hit x / p ≤ M / Y i :=
      (Nat.div_le_div_right (hD _ hn).2).trans (Nat.div_le_div_left hpY (by omega))
    exact mem_biUnion.mpr ⟨i, hi, mem_biUnion.mpr ⟨p,
      mem_filter.mpr ⟨hp, hit x, hn, hdvd⟩, mem_image.mpr
        ⟨hit x / p, mem_Icc.mpr ⟨hq0, hqb⟩, Nat.div_mul_cancel hdvd⟩⟩⟩
  have hinj : Set.InjOn hit (↑S : Set ℕ) := by
    intro x hx y hy heq
    by_contra hne
    rcases (hhit x hx).2 with hx' | hx' <;> rcases (hhit y hy).2 with hy' | hy' <;>
      rcases hsep x hx y hy hne with h | h <;> omega
  have hcand (i : ℕ) (hi : i ∈ J) : (candidates i).card ≤ (M / Y i) * ((F i).card * K i) := by
    calc
      (candidates i).card ≤ ∑ p ∈ used i, (multiples i p).card := card_biUnion_le
      _ ≤ ∑ _ ∈ used i, M / Y i := sum_le_sum fun p _ =>
        card_image_le.trans (by simp)
      _ = (M / Y i) * (used i).card := by simp [mul_comm]
      _ ≤ (M / Y i) * ((F i).card * K i) := Nat.mul_le_mul_left _ (hused i hi)
  have htotal : S.card ≤ ∑ i ∈ J, (M / Y i) * ((F i).card * K i) := calc
    S.card ≤ (J.biUnion candidates).card := card_le_card_of_injOn hit hcover hinj
    _ ≤ ∑ i ∈ J, (candidates i).card := card_biUnion_le
    _ ≤ _ := sum_le_sum hcand
  exact (not_lt_of_ge htotal) hmany

