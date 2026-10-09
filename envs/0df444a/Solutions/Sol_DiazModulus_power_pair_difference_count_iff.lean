-- Prove2me | solution 1 for DiazModulus.power_pair_difference_count_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-08T16:42:34.949198+00:00
-- url     : https://prove2.me/submissions/ad497566-de79-4af6-be24-5b25e6da7332

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Three equal differences in `{0, ±1, ±k, ±l}`

For `4 ≤ k < l` and `S = {0, ±1, ±k, ±l}`, some `d > 0` has `#{s ∈ S | s + d ∈ S} ≥ 3` iff
`l ∈ {k + 1, k + 2, 2k − 1, 2k, 2k + 1, 3k}`.

`⇐`: explicit witnesses, e.g. `l = 2k` with `d = k` and `s ∈ {0, −k, k}`; `three_le` turns three
distinct elements of the filter into the bound.
`⇒`: since `S = −S`, the map `s ↦ −s − d` is an involution of the filter, so among three distinct
elements there are two, `x` and `y`, with `y ≠ x` and `y ≠ −x − d` (`exists_pair`). The pairs
`(x, x + d)` and `(y, y + d)` then realise the same difference twice without being exchanged by the
involution, which forces a coincidence among the positive differences `1, 2, k − 1, k, k + 1, 2k,
l − k, l − 1, l, l + 1, l + k, 2l`. The case analysis (`key`) runs over `x, x + d ∈ S` (pruning
`d ≤ 0` early) and then over `y, y + d ∈ S`; every one of the ~10³ leaves closes by `omega`.
-/

namespace R6_powerPairDiff

/-- Three distinct elements of the filter give two elements `x, y` with `y ≠ x` and
`y ≠ -x - d` (the partner of `x` under the involution `s ↦ -s - d`). -/
theorem exists_pair {S : Finset ℤ} {d : ℤ} (h : 3 ≤ (S.filter (fun s => s + d ∈ S)).card) :
    ∃ x y, x ∈ S ∧ x + d ∈ S ∧ y ∈ S ∧ y + d ∈ S ∧ y ≠ x ∧ y ≠ -x - d := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 (Nat.lt_of_lt_of_le (by norm_num) h)
  rw [Finset.mem_filter] at ha hb hc
  by_cases hb' : b = -a - d
  · exact ⟨a, c, ha.1, ha.2, hc.1, hc.2, Ne.symm hac, by rw [← hb']; exact Ne.symm hbc⟩
  · exact ⟨a, b, ha.1, ha.2, hb.1, hb.2, Ne.symm hab, hb'⟩

/-- Three explicit elements of the filter give the bound `3 ≤ #filter`. -/
theorem three_le {S : Finset ℤ} (d a b c : ℤ) (ha : a ∈ S) (ha' : a + d ∈ S) (hb : b ∈ S)
    (hb' : b + d ∈ S) (hc : c ∈ S) (hc' : c + d ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ (S.filter (fun s => s + d ∈ S)).card := by
  have hsub : ({a, b, c} : Finset ℤ) ⊆ S.filter (fun s => s + d ∈ S) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [Finset.mem_filter]
    rcases hz with rfl | rfl | rfl
    exacts [⟨ha, ha'⟩, ⟨hb, hb'⟩, ⟨hc, hc'⟩]
  calc 3 = ({a, b, c} : Finset ℤ).card := (Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- The case analysis: a pair `x, y` as in `exists_pair` forces one of the six relations. -/
theorem key (k l d : ℤ) (hk : 4 ≤ k) (hkl : k < l) (hd : 0 < d) (x : ℤ)
    (hx : x = 0 ∨ x = 1 ∨ x = -1 ∨ x = k ∨ x = -k ∨ x = l ∨ x = -l)
    (hx' : x + d = 0 ∨ x + d = 1 ∨ x + d = -1 ∨ x + d = k ∨ x + d = -k ∨ x + d = l ∨ x + d = -l) :
    ∀ y, (y = 0 ∨ y = 1 ∨ y = -1 ∨ y = k ∨ y = -k ∨ y = l ∨ y = -l) →
    (y + d = 0 ∨ y + d = 1 ∨ y + d = -1 ∨ y + d = k ∨ y + d = -k ∨ y + d = l ∨ y + d = -l) →
    y ≠ x → y ≠ -x - d →
    (l = k + 1 ∨ l = k + 2 ∨ l = 2 * k - 1 ∨ l = 2 * k ∨ l = 2 * k + 1 ∨ l = 3 * k) := by
  rcases hx with h1|h1|h1|h1|h1|h1|h1 <;> rcases hx' with h2|h2|h2|h2|h2|h2|h2 <;>
    (try (exfalso; omega)) <;>
    intro y hy hy' hne1 hne2 <;>
    rcases hy with h3|h3|h3|h3|h3|h3|h3 <;> rcases hy' with h4|h4|h4|h4|h4|h4|h4 <;> omega

end R6_powerPairDiff

open DiazModulus R6_powerPairDiff in
theorem solution (k l : ℤ) (hk : 4 ≤ k) (hkl : k < l) :
    (∃ d : ℤ, 0 < d ∧ 3 ≤ (({0, 1, -1, k, -k, l, -l} : Finset ℤ).filter
      (fun s => s + d ∈ ({0, 1, -1, k, -k, l, -l} : Finset ℤ))).card) ↔
    (l = k + 1 ∨ l = k + 2 ∨ l = 2 * k - 1 ∨ l = 2 * k ∨ l = 2 * k + 1 ∨ l = 3 * k) := by
  constructor
  · rintro ⟨d, hd, h⟩
    obtain ⟨x, y, hx, hx', hy, hy', hne1, hne2⟩ := exists_pair h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx' hy hy'
    exact key k l d hk hkl hd x hx hx' y hy hy' hne1 hne2
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨1, by omega, three_le 1 (-1) 0 k ?_ ?_ ?_ ?_ ?_ ?_ (by omega) (by omega) (by omega)⟩ <;>
        simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega
    · refine ⟨2, by omega, three_le 2 (-1) k (-(k + 2)) ?_ ?_ ?_ ?_ ?_ ?_ (by omega) (by omega)
        (by omega)⟩ <;> simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega
    · refine ⟨k - 1, by omega, three_le (k - 1) 1 (-k) k ?_ ?_ ?_ ?_ ?_ ?_ (by omega) (by omega)
        (by omega)⟩ <;> simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega
    · refine ⟨k, by omega, three_le k 0 (-k) k ?_ ?_ ?_ ?_ ?_ ?_ (by omega) (by omega)
        (by omega)⟩ <;> simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega
    · refine ⟨k + 1, by omega, three_le (k + 1) (-1) (-k) k ?_ ?_ ?_ ?_ ?_ ?_ (by omega) (by omega)
        (by omega)⟩ <;> simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega
    · refine ⟨2 * k, by omega, three_le (2 * k) (-k) k (-(3 * k)) ?_ ?_ ?_ ?_ ?_ ?_ (by omega)
        (by omega) (by omega)⟩ <;> simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true] <;> omega
