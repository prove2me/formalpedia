-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_uniform_affine_generator_integrand_crossing_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:17:38.812659+00:00
-- url     : https://prove2.me/submissions/875f68a1-62ec-4ec6-9056-37286d41d2b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
theorem solution
    (y z : ℝ) (hy : 0 < y) (hz : z ∈ Ioo (-1 : ℝ) 0)
    (w : ℝ → ℝ)
    (hw : ∀ u : ℝ, w u = if u < 0 then 0 else 1 / 2 + u)
    (hd : deriv w y = 1) :
    SpectrallyNegativeLevy.generatorIntegrand w y z =
      if y + z < 0 then -(y + (1 / 2 : ℝ) + z) else 0 := by
  have hz' : z ∈ Ioo (-1 : ℝ) 1 := ⟨hz.1, lt_trans hz.2 (by norm_num)⟩
  simp only [SpectrallyNegativeLevy.generatorIntegrand]
  rw [hw y, hw (y + z), hd]
  simp only [Set.indicator_of_mem hz', Pi.one_apply]
  have hnot : ¬ y < 0 := not_lt.mpr (le_of_lt hy)
  by_cases hcross : y + z < 0
  · simp only [hnot, hcross, if_false, if_true]
    ring
  · simp only [hnot, hcross, if_false]
    ring
