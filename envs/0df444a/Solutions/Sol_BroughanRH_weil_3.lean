-- Prove2me | solution 3 for BroughanRH.weil
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:33:56.439114+00:00
-- url     : https://prove2.me/submissions/bd261fcb-89bc-4359-8dd2-520bd62983d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_ConnesRZ_weil_positivity_of_RH

theorem solution :
    ∀ g : ℝ → ℂ, ConnesRZ.IsTest g → 0 ≤ (ConnesRZ.weilDistribution (ConnesRZ.conv g (ConnesRZ.starInv g))).re := by
  intro g hg
  refine ConnesRZ.weil_positivity_of_RH ?_ g hg
  intro s ⟨hz, h0, h1⟩
  refine riemann_hypothesis s hz ?_ ?_
  · rintro ⟨n, rfl⟩
    simp at h0
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith
  · rintro rfl; simp at h1
