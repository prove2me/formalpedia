-- Prove2me | solution 1 for Erdos287.opposite_parity_holes_enclose_even_run
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:59:59.249913+00:00
-- url     : https://prove2.me/submissions/0ae88058-9fd0-4683-b3cc-d17bc61a3f79

import Mathlib

open Finset

set_option autoImplicit false

/-- Opposite-parity holes enclose a maximal selected run of even length. -/
theorem solution (H : Finset ℕ) (a b : ℕ) (ha : a ∈ H) (hb : b ∈ H) (hab : a < b)
    (hp : a % 2 ≠ b % 2) (hsep : ∀ n ∈ H, n + 1 ∉ H) :
    ∃ x ∈ H, ∃ y ∈ H, a ≤ x ∧ y ≤ b ∧ x + 3 ≤ y ∧ Even (y - x - 1) ∧
      ∀ n, x < n → n < y → n ∉ H := by
  classical
  let later := H.filter (fun n => a < n ∧ n ≤ b ∧ n % 2 ≠ a % 2)
  have hne : later.Nonempty := ⟨b, mem_filter.mpr ⟨hb, hab, le_rfl, Ne.symm hp⟩⟩
  let y := later.min' hne
  have hy : y ∈ later := min'_mem _ _
  obtain ⟨hyH, hay, hyb, hymod⟩ := mem_filter.mp hy
  let earlier := H.filter (fun n => a ≤ n ∧ n < y)
  have hne' : earlier.Nonempty := ⟨a, mem_filter.mpr ⟨ha, le_rfl, hay⟩⟩
  let x := earlier.max' hne'
  have hx : x ∈ earlier := max'_mem _ _
  obtain ⟨hxH, hax, hxy⟩ := mem_filter.mp hx
  have hxmod : x % 2 = a % 2 := by
    by_contra hneMod
    have hax' : a < x := by omega
    have hxl : x ∈ later := mem_filter.mpr ⟨hxH, hax', hxy.le.trans hyb, hneMod⟩
    exact hxy.not_ge (min'_le _ _ hxl)
  have hgap : x + 1 ≠ y := fun h => hsep x hxH (h.symm ▸ hyH)
  refine ⟨x, hxH, y, hyH, hax, hyb, by omega, ?_, ?_⟩
  · apply Nat.even_iff.mpr
    omega
  · intro n hxn hny hn
    have hnearlier : n ∈ earlier := mem_filter.mpr ⟨hn, hax.trans hxn.le, hny⟩
    exact hxn.not_ge (le_max' _ _ hnearlier)

