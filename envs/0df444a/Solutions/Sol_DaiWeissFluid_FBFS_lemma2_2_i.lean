-- Prove2me | solution 1 for DaiWeissFluid.FBFS.lemma2_2_i
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:52:23.383985+00:00
-- url     : https://prove2.me/submissions/b5728881-a893-43ec-b407-bfc2a972de05

import Mathlib

set_option autoImplicit false

theorem solution (g : ℝ → ℝ) (hg : ∀ s, 0 ≤ s → 0 ≤ g s)
    (t : ℝ) (ht : 0 < t) (h0 : g t = 0) (d : ℝ)
    (hd : HasDerivAt g d t) : d = 0 := by
  have hmin : IsLocalMin g t := by
    filter_upwards [lt_mem_nhds ht] with y hy
    rw [h0]
    exact hg y hy.le
  exact hmin.hasDerivAt_eq_zero hd
