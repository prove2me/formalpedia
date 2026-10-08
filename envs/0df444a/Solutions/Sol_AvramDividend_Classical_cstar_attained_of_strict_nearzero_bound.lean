-- Prove2me | solution 1 for AvramDividend.Classical.cstar_attained_of_strict_nearzero_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T20:45:42.824123+00:00
-- url     : https://prove2.me/submissions/a14415e1-2757-486c-a82e-244a398824af

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_attained_of_compact_initial_minimizers

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set

theorem solution (W : ℝ → ℝ) (a δ : ℝ)
    (ha : a ∈ cstarSet W)
    (hδ : 0 < δ) (hδa : δ ≤ a)
    (hcont : ContinuousOn (deriv W) (Set.Icc δ a))
    (hnear : ∀ x : ℝ, 0 < x → x < δ →
      deriv W a < deriv W x) :
    (cstar W).toReal ∈ cstarSet W := by
  have heq : cstarSet W ∩ Set.Icc 0 a =
      Set.Icc δ a ∩ (deriv W ⁻¹' Set.Iic (deriv W a)) := by
    ext x
    constructor
    · rintro ⟨hx, hxa⟩
      have hδx : δ ≤ x := by
        by_contra hn
        have hlt : x < δ := lt_of_not_ge hn
        have hstrict : deriv W a < deriv W x := hnear x hx.1 hlt
        exact (not_le_of_gt hstrict) (hx.2 a ha.1)
      exact ⟨⟨hδx, hxa.2⟩, hx.2 a ha.1⟩
    · rintro ⟨⟨hxδ, hxa⟩, hxle⟩
      have hxpos : 0 < x := lt_of_lt_of_le hδ hxδ
      have hglob : ∀ y : ℝ, 0 < y → deriv W x ≤ deriv W y := by
        intro y hy
        exact hxle.trans (ha.2 y hy)
      exact ⟨⟨hxpos, hglob⟩, ⟨hxpos.le, hxa⟩⟩
  have hclosed : IsClosed
      (Set.Icc δ a ∩ (deriv W ⁻¹' Set.Iic (deriv W a))) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hcompact : IsCompact (cstarSet W ∩ Set.Icc 0 a) := by
    rw [heq]
    exact isCompact_Icc.of_isClosed_subset hclosed Set.inter_subset_left
  exact cstar_attained_of_compact_initial_minimizers W a ha hcompact
