-- Prove2me | solution 1 for CirclePackingConstants.sixteen_cover_group2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-06T15:08:54.123369+00:00
-- url     : https://prove2.me/submissions/148670c1-1121-406f-a0a9-b93c9451acec

import Definitions.Def_CirclePackingConstants
import Definitions.Def_CirclePackingConstants_SixteenOcc
import Theorems.Thm_CirclePackingConstants_sixteen_cover_g2a
import Theorems.Thm_CirclePackingConstants_sixteen_cover_g2b

open CirclePackingConstants CirclePackingConstants.Sixteen

theorem solution (n : ℕ → ℕ) (hn : ∀ i, n i ≤ 2) (hsum : ∑ i ∈ Finset.range 16, n i = 16) (hne : ∃ i < 16, n i ≠ 1)
    (hab : (n 0 = 0 ∧ n 1 = 1)) :
    ∃ e s tx ty, Sixteen.Matches Sixteen.sixteenLib n e s tx ty := by
  obtain ⟨ha, hb⟩ := hab
  have h2 := hn 2
  rcases (by omega : n 2 = 0 ∨ n 2 = 1 ∨ n 2 = 2) with hc | hc | hc
  · exact sixteen_cover_g2a n hn hsum hne (Or.inl ⟨ha, hb, hc⟩)
  · exact sixteen_cover_g2b n hn hsum hne ⟨ha, hb, hc⟩
  · exact sixteen_cover_g2a n hn hsum hne (Or.inr ⟨ha, hb, hc⟩)
