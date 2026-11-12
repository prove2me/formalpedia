-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb80_uniform_refinement_index_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:46:29.795194+00:00
-- url     : https://prove2.me/submissions/fc022e21-44bb-431b-a9ff-dddb694e3c75

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A refined grid index lies inside the coarse block selected by its quotient. -/
theorem solution (m p r : ℕ) (hr : r < (m + 1) * (p + 1)) :
    r / (p + 1) ≤ m ∧
    (r / (p + 1)) * (p + 1) ≤ r ∧
    r < (r / (p + 1) + 1) * (p + 1) := by
  have hp : 0 < p + 1 := Nat.succ_pos p
  have hi : r / (p + 1) < m + 1 :=
    (Nat.div_lt_iff_lt_mul hp).2 hr
  have hleft : r / (p + 1) * (p + 1) ≤ r :=
    Nat.div_mul_le_self r (p + 1)
  have hm := Nat.mod_lt r hp
  have hd := Nat.mod_add_div r (p + 1)
  refine ⟨by omega, hleft, ?_⟩
  nlinarith
