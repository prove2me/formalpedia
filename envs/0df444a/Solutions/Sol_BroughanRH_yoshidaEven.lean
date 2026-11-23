-- Prove2me | solution 1 for BroughanRH.yoshidaEven
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:33:57.003099+00:00
-- url     : https://prove2.me/submissions/d8d6e6c9-77a0-4101-8036-100c0ffd3060
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_ConnesRZ_weil_positivity_of_RH

theorem solution :
    ∀ f : ℝ → ℂ, ConnesRZ.IsTest f → (∀ x : ℝ, f (-x) = f x) → 0 ≤ (ConnesRZ.weilDistribution (ConnesRZ.conv f (ConnesRZ.starInv f))).re := by
  intro g hg _
  refine ConnesRZ.weil_positivity_of_RH ?_ g hg
  intro s ⟨hz, h0, h1⟩
  refine riemann_hypothesis s hz ?_ ?_
  · rintro ⟨n, rfl⟩
    simp at h0
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith
  · rintro rfl; simp at h1
