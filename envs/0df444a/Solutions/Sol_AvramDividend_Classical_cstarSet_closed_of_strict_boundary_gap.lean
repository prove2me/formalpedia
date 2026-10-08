-- Prove2me | solution 1 for AvramDividend.Classical.cstarSet_closed_of_strict_boundary_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T15:39:15.60352+00:00
-- url     : https://prove2.me/submissions/ca330bf6-539b-4b8d-b7b3-34a6fb4aec5d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical

theorem solution (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Set.Ici (0 : ℝ)))
    (a : ℝ) (ha : a ∈ cstarSet W)
    (hgap : deriv W a < deriv W 0) :
    IsClosed (cstarSet W) := by
  have heq : cstarSet W =
      Set.Ici (0 : ℝ) ∩ (deriv W ⁻¹' Set.Iic (deriv W a)) := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.le, hx.2 a ha.1⟩
    · rintro ⟨hx0, hxle⟩
      have hxne : x ≠ 0 := by
        intro hzero
        subst x
        exact (not_le_of_gt hgap) hxle
      have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxne)
      have hxeq : deriv W x = deriv W a :=
        le_antisymm hxle (ha.2 x hxpos)
      exact ⟨hxpos, by
        intro y hy
        rw [hxeq]
        exact ha.2 y hy⟩
  rw [heq]
  exact hcont.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic
