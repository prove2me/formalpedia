-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_finite_ENNReal_tendsto_from_real_cast_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:24:40.931121+00:00
-- url     : https://prove2.me/submissions/f2b46903-930b-49b2-8a3b-7739311e8490

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (g : ℕ → ℝ≥0∞) (x : ℝ≥0∞)
    (hfin : ∀ n, g n ≠ ⊤) (hx : x ≠ ⊤)
    (h : Tendsto (fun n => (g n).toReal) atTop (𝓝 x.toReal)) :
    Tendsto g atTop (𝓝 x) := by
  have ht := ENNReal.continuous_ofReal.tendsto x.toReal
  have hcomp : Tendsto (fun n => ENNReal.ofReal ((g n).toReal))
      atTop (𝓝 (ENNReal.ofReal x.toReal)) := ht.comp h
  have hfun : (fun n => ENNReal.ofReal ((g n).toReal)) = g := by
    funext n
    exact ENNReal.ofReal_toReal (hfin n)
  rw [hfun, ENNReal.ofReal_toReal hx] at hcomp
  exact hcomp
