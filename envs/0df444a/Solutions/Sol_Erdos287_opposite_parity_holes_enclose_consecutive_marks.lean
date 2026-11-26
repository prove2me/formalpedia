-- Prove2me | solution 1 for Erdos287.opposite_parity_holes_enclose_consecutive_marks
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T09:24:45.713199+00:00
-- url     : https://prove2.me/submissions/37ace354-783a-4b97-affc-83dcac4de4a2

import Mathlib

open Finset

set_option autoImplicit false

/-- Two opposite-parity holes in a set meeting every adjacent pair enclose
two consecutive marked positions. -/
theorem solution (D : Finset ℕ) (x y : ℕ) (hxy : x < y)
    (hparity : x % 2 ≠ y % 2) (hx : x ∉ D) (hy : y ∉ D)
    (hcover : ∀ n, x ≤ n → n < y → n ∈ D ∨ n + 1 ∈ D) :
    ∃ n, x < n ∧ n + 1 < y ∧ n ∈ D ∧ n + 1 ∈ D := by
  by_contra! hfail
  have halt (r : ℕ) (hr : x + r ≤ y) : x + r ∈ D ↔ r % 2 = 1 := by
    induction r with
    | zero => simp [hx]
    | succ r ih =>
      have hle : x + r ≤ y := by omega
      have hlt : x + r < y := by omega
      have hc := hcover (x + r) (Nat.le_add_right _ _) hlt
      have hdisj : x + r ∈ D → x + r + 1 ∉ D := by
        intro hn hn'
        have hxlt : x < x + r := by
          by_contra! h
          have he : x + r = x := by omega
          exact hx (he ▸ hn)
        have hylt : x + r + 1 < y := by
          by_contra! h
          have he : x + r + 1 = y := by omega
          exact hy (he ▸ hn')
        exact hfail (x + r) hxlt hylt hn hn'
      have hevenodd : x + r + 1 ∈ D ↔ x + r ∉ D :=
        ⟨fun ha hb => hdisj hb ha, fun h => hc.resolve_left h⟩
      rw [Nat.add_succ, hevenodd, ih hle]
      omega
  have he : x + (y - x) = y := Nat.add_sub_cancel' hxy.le
  have ho : (y - x) % 2 = 1 := by omega
  exact hy (he ▸ (halt (y - x) (he.trans_le le_rfl)).mpr ho)

