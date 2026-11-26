-- Prove2me | solution 1 for Erdos287.short_inverse_frequency_bound_with_repeated_prime_labels
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:20:02.576098+00:00
-- url     : https://prove2.me/submissions/80bb4ca0-0b61-4419-a9a1-efb900413bd7

import Mathlib
import Theorems.Thm_Erdos287_short_inverse_frequencies_have_few_large_prime_labels

open Finset

set_option autoImplicit false

/-- The short-arc bound for large prime labels also applies when a label is
used at several of its multiples. -/
theorem solution (D : Finset ℕ) (label : ℕ → ℕ) (M q a R Y K : ℕ)
    (ha : 0 < a) (haq : a < q) (hY : 2 ≤ Y)
    (hD : ∀ n ∈ D, 0 < n ∧ n ≤ M ∧ (label n).Prime ∧ Y ≤ label n ∧ label n ∣ n)
    (hphase : ∀ n ∈ D, ∃ r ≤ R, n * r ≡ a [MOD q] ∨ n * r ≡ q - a [MOD q])
    (hsize : (M * R / q + 1) * q < Y ^ (K + 1)) :
    D.card ≤ 2 * (M * R / q + 1) * K * (M / Y) := by
  classical
  let P := D.image label
  have hreps (r : ℕ) (hr : r ∈ P) : ∃ n ∈ D, label n = r := mem_image.mp hr
  choose pick hpickD hpickLabel using hreps
  let S := P.attach.image (fun r => pick r.val r.property)
  have hS : S ⊆ D := by
    intro n hn
    obtain ⟨r, _, rfl⟩ := mem_image.mp hn
    exact hpickD r.val r.property
  have hSinj : Set.InjOn label (↑S : Set ℕ) := by
    intro n hn m hm h
    obtain ⟨r, _, rfl⟩ := mem_image.mp hn
    obtain ⟨s, _, rfl⟩ := mem_image.mp hm
    rw [hpickLabel, hpickLabel] at h
    have hrs : r = s := Subtype.ext h
    subst s
    rfl
  have hSimage : S.image label = P := by
    ext p
    constructor
    · intro hp
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hp
      exact mem_image.mpr ⟨n, hS hn, rfl⟩
    · intro hp
      refine mem_image.mpr ⟨pick p hp, ?_, hpickLabel p hp⟩
      exact mem_image.mpr ⟨⟨p, hp⟩, mem_attach _ _, rfl⟩
  have hPbound : P.card ≤ 2 * (M * R / q + 1) * K := by
    rw [← hSimage, card_image_of_injOn hSinj]
    exact Erdos287.short_inverse_frequencies_have_few_large_prime_labels S label M q a R Y K
      ha haq hY (fun n hn => (hD n (hS hn)).2) hSinj (fun n hn => hphase n (hS hn)) hsize
  have hfiber (p : ℕ) (hp : p ∈ P) : (D.filter (fun n => label n = p)).card ≤ M / Y := by
    let F := D.filter (fun n => label n = p)
    obtain ⟨n₀, hn₀, hlabel⟩ := mem_image.mp hp
    have hpY : Y ≤ p := hlabel ▸ (hD n₀ hn₀).2.2.2.1
    have hd (n : ℕ) (hn : n ∈ F) : n / p * p = n := by
      obtain ⟨hnD, hnp⟩ := mem_filter.mp hn
      exact Nat.div_mul_cancel (hnp ▸ (hD n hnD).2.2.2.2)
    have hm : Set.MapsTo (fun n => n / p) (↑F : Set ℕ) (↑(Icc 1 (M / Y)) : Set ℕ) := by
      intro n hn
      have hnD := (mem_filter.mp hn).1
      have hnpos : 0 < n / p := by
        by_contra! h
        have hz : n / p = 0 := Nat.eq_zero_of_le_zero h
        have he := hd n hn
        rw [hz, zero_mul] at he
        exact (hD n hnD).1.ne' he.symm
      have hquot : n / p ≤ M / Y := (Nat.le_div_iff_mul_le (by omega : 0 < Y)).mpr
        ((Nat.mul_le_mul_left (n / p) hpY).trans ((hd n hn).trans_le (hD n hnD).2.1))
      exact mem_Icc.mpr ⟨hnpos, hquot⟩
    have hi : Set.InjOn (fun n => n / p) (↑F : Set ℕ) := by
      intro n hn m hm he
      change n / p = m / p at he
      calc
        n = n / p * p := (hd n hn).symm
        _ = m / p * p := by rw [he]
        _ = m := hd m hm
    simpa using card_le_card_of_injOn (fun n => n / p) hm hi
  calc
    D.card = ∑ p ∈ P, (D.filter (fun n => label n = p)).card := card_eq_sum_card_image _ _
    _ ≤ ∑ _ ∈ P, M / Y := sum_le_sum hfiber
    _ = P.card * (M / Y) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hPbound

