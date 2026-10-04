-- Prove2me | solution 1 for ClassicalSchur.even_of_frontier
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-04T00:31:05.080914+00:00
-- url     : https://prove2.me/submissions/8698bea8-a104-42a9-a939-43383266bd09

-- Generated from lean/ClassicalSchur/Midpoint.lean
--   imports : 1 platform node(s), 2 definition bundle(s)
--   inlined : 2 file-scoped / sub-threshold helper(s)
--   rename  : even_of_frontier -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurColoring
import Definitions.Def_ClassicalSchurRamsey
import Theorems.Thm_ClassicalSchur_endpointNbhd_of_frontier
import Mathlib

open Finset

namespace ClassicalSchur

/-- Membership in a colour neighbourhood. -/
theorem mem_colorNbhd {n : ℕ} {c : ℕ → Fin n} {V : Finset ℕ} {v w : ℕ} {i : Fin n} :
    w ∈ colorNbhd c V v i ↔ w ≠ v ∧ w ∈ V ∧ c (Nat.dist v w) = i := by
  simp [colorNbhd, and_assoc]

/-- Membership in the central neighbourhood: `x ∈ [0, 2m + 1]`, `x ≠ m`, and
`c |m − x| = c (m + 1)`. -/
theorem mem_centralNbhd {n : ℕ} {c : ℕ → Fin n} {m x : ℕ} :
    x ∈ centralNbhd c m ↔ x ≠ m ∧ x ≤ 2 * m + 1 ∧ c (Nat.dist m x) = c (m + 1) := by
  rw [centralNbhd, mem_colorNbhd, mem_range, Nat.lt_succ_iff]

end ClassicalSchur

open ClassicalSchur in
theorem solution {k u t m : ℕ} (hR : TriangleRamsey k (u + 1))
    (h2t : 2 * t = (k + 1) * u) (hm : m = (k + 2) * t) {c : ℕ → Fin (k + 2)}
    (hc : SchurColoring (2 * m + 1) c) : Even u := by
  obtain ⟨i, hi⟩ := exists_ne (c (m + 1))
  obtain ⟨hcard, hrefl, -⟩ := endpointNbhd_of_frontier hR h2t hm hc hi
  set P := endpointNbhd c m i with hP
  have hle : ∀ x ∈ P, x ≤ 2 * m := fun x hx => by
    obtain ⟨hxN, hxV, -⟩ := mem_colorNbhd.mp hx
    have := (mem_centralNbhd.mp hxV).2.1
    omega
  have hhalf : (P.filter fun x => ¬ x < m).card = (P.filter fun x => x < m).card := by
    apply card_nbij' (fun x => 2 * m - x) (fun x => 2 * m - x)
    · intro x hx
      obtain ⟨hxP, hxm⟩ := mem_filter.mp hx
      obtain ⟨hJ, hJx⟩ := hrefl x hxP
      have := hle x hxP
      change 2 * m - x ∈ P.filter fun x => x < m
      exact mem_filter.mpr ⟨hJ, by omega⟩
    · intro x hx
      obtain ⟨hxP, hxm⟩ := mem_filter.mp hx
      obtain ⟨hJ, -⟩ := hrefl x hxP
      change 2 * m - x ∈ P.filter fun x => ¬ x < m
      exact mem_filter.mpr ⟨hJ, by omega⟩
    · intro x hx
      have := hle x (mem_filter.mp hx).1
      change 2 * m - (2 * m - x) = x
      omega
    · intro x hx
      have := hle x (mem_filter.mp hx).1
      change 2 * m - (2 * m - x) = x
      omega
  have hsplit := card_filter_add_card_filter_not (s := P) fun x => x < m
  exact ⟨(P.filter fun x => x < m).card, by omega⟩
