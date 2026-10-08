-- Prove2me | solution 1 for AvramDividend.Classical.cstarSet_closed_of_near_zero_deriv_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T16:34:08.861982+00:00
-- url     : https://prove2.me/submissions/08868da7-7bb6-4a0d-b18f-5b9fbbce9b04

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical

theorem solution (W : ℝ → ℝ) (a δ : ℝ)
    (ha : a ∈ cstarSet W)
    (hδ : 0 < δ)
    (hgap : ∀ x : ℝ, 0 < x → x < δ → deriv W a < deriv W x)
    (hcont : ContinuousOn (deriv W) (Set.Ioi (0 : ℝ))) :
    IsClosed (cstarSet W) := by
  have heq : cstarSet W =
      Set.Ici δ ∩ ((deriv W) ⁻¹' Set.Iic (deriv W a)) := by
    ext x
    constructor
    · intro hx
      have hxδ : δ ≤ x := by
        by_contra hnot
        have hxlt : x < δ := lt_of_not_ge hnot
        exact (not_le_of_gt (hgap x hx.1 hxlt)) (hx.2 a ha.1)
      exact ⟨hxδ, hx.2 a ha.1⟩
    · rintro ⟨hxδ, hxle⟩
      have hxpos : 0 < x := lt_of_lt_of_le hδ hxδ
      have hxeq : deriv W x = deriv W a :=
        le_antisymm hxle (ha.2 x hxpos)
      refine ⟨hxpos, ?_⟩
      intro y hy
      rw [hxeq]
      exact ha.2 y hy
  rw [heq]
  have hsub : Set.Ici δ ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_lt_of_le hδ hx
  exact (hcont.mono hsub).preimage_isClosed_of_isClosed
    isClosed_Ici isClosed_Iic
