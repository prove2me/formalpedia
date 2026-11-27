-- Prove2me | solution 1 for Erdos287.min_card_reciprocal_merge_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T23:42:47.430334+00:00
-- url     : https://prove2.me/submissions/ce802770-2f48-4cb5-83eb-c37ffbe926d1

import Mathlib

open Finset

set_option autoImplicit false

/-- In a minimum-cardinality exact reciprocal sum with no adjacent omissions,
two separated denominators cannot merge into a hole without a second hole
adjacent to a denominator that the merge would delete. -/
theorem solution (D : Finset ℕ) (m M a b c : ℕ)
    (hm : m ∈ D) (hD : D ⊆ Finset.Icc m M)
    (hcover : ∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hmin : ∀ E : Finset ℕ, m ∈ E → E ⊆ Finset.Icc m M →
      (∀ x, m ≤ x → x + 1 ≤ M → x ∈ E ∨ x + 1 ∈ E) →
      (∑ n ∈ E, (1 : ℚ) / n = 1) → D.card ≤ E.card)
    (ha : a ∈ D) (hb : b ∈ D) (hma : m < a) (hab : a + 2 ≤ b)
    (hc : c ∈ Finset.Icc m M) (hcD : c ∉ D)
    (hmerge : (1 : ℚ) / a + 1 / b = 1 / c) :
    ∃ x ∈ Finset.Icc m M, x ∉ D ∧ x ≠ c ∧
      (x + 1 = a ∨ a + 1 = x ∨ x + 1 = b ∨ b + 1 = x) := by
  classical
  by_contra hbad
  let R := (D.erase a).erase b
  let E := insert c R
  have hne : b ≠ a := by omega
  have hb' : b ∈ D.erase a := mem_erase.mpr ⟨hne, hb⟩
  have hR : R ⊆ D := fun _ hx => mem_of_mem_erase (mem_of_mem_erase hx)
  have hcR : c ∉ R := fun hx => hcD (hR hx)
  have hmE : m ∈ E := by
    apply mem_insert_of_mem
    exact mem_erase.mpr ⟨by omega, mem_erase.mpr ⟨by omega, hm⟩⟩
  have hE : E ⊆ Finset.Icc m M := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hc
    · exact hD (hR hx)
  have keep (x : ℕ) (hx : x ∈ D) (hxa : x ≠ a) (hxb : x ≠ b) : x ∈ E :=
    mem_insert_of_mem (mem_erase.mpr ⟨hxb, mem_erase.mpr ⟨hxa, hx⟩⟩)
  have neighbor (x : ℕ) (hx : x ∈ Finset.Icc m M) (hxa : x ≠ a) (hxb : x ≠ b)
      (hn : x + 1 = a ∨ a + 1 = x ∨ x + 1 = b ∨ b + 1 = x) : x ∈ E := by
    by_cases hxc : x = c
    · exact mem_insert.mpr (Or.inl hxc)
    · by_cases hxD : x ∈ D
      · exact keep x hxD hxa hxb
      · exact (hbad ⟨x, hx, hxD, hxc, hn⟩).elim
  have hcoverE (x : ℕ) (hx : m ≤ x) (hxM : x + 1 ≤ M) :
      x ∈ E ∨ x + 1 ∈ E := by
    rcases hcover x hx hxM with hxD | hxD
    · by_cases hxa : x = a
      · exact Or.inr (neighbor (x + 1) (mem_Icc.mpr ⟨by omega, hxM⟩)
          (by omega) (by omega) (Or.inr (Or.inl (by omega))))
      · by_cases hxb : x = b
        · exact Or.inr (neighbor (x + 1) (mem_Icc.mpr ⟨by omega, hxM⟩)
            (by omega) (by omega) (Or.inr (Or.inr (Or.inr (by omega)))))
        · exact Or.inl (keep x hxD hxa hxb)
    · by_cases hxa : x + 1 = a
      · exact Or.inl (neighbor x (mem_Icc.mpr ⟨hx, by omega⟩)
          (by omega) (by omega) (Or.inl hxa))
      · by_cases hxb : x + 1 = b
        · exact Or.inl (neighbor x (mem_Icc.mpr ⟨hx, by omega⟩)
            (by omega) (by omega) (Or.inr (Or.inr (Or.inl hxb))))
        · exact Or.inr (keep (x + 1) hxD hxa hxb)
  have hsumA := sum_erase_add D (fun n => (1 : ℚ) / n) ha
  have hsumB := sum_erase_add (D.erase a) (fun n => (1 : ℚ) / n) hb'
  have hsumE : ∑ n ∈ E, (1 : ℚ) / n = 1 := by
    rw [show E = insert c R from rfl, sum_insert hcR]
    change (∑ n ∈ R, (1 : ℚ) / n) + 1 / b =
      ∑ n ∈ D.erase a, (1 : ℚ) / n at hsumB
    linarith
  have hcard := hmin E hmE hE hcoverE hsumE
  have hcardA := card_erase_add_one ha
  have hcardB := card_erase_add_one hb'
  have hcardE : E.card = R.card + 1 := card_insert_of_notMem hcR
  change R.card + 1 = (D.erase a).card at hcardB
  omega

