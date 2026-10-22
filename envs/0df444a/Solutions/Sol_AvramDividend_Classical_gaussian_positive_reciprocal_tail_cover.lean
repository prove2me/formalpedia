-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_positive_reciprocal_tail_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:13:23.679408+00:00
-- url     : https://prove2.me/submissions/cd2f28f6-6107-4233-9539-45f6062c18a1

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Interval.Set.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- The nonpositive half-line and reciprocal positive tails span the real line. -/
theorem solution :
    (⋃ n : ℕ, if n = 0 then Iic (0 : ℝ)
      else Ici ((n : ℝ)⁻¹)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ≤ 0
  · exact Set.mem_iUnion.mpr ⟨0, by simpa using hx⟩
  · obtain ⟨n, hn, hnx⟩ :=
      Real.exists_nat_pos_inv_lt (lt_of_not_ge hx)
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    simpa [Nat.ne_of_gt hn] using (le_of_lt hnx)
