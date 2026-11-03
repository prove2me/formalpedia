-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_predictable_source_negative_mark_ruin_overshoot_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:07:25.168229+00:00
-- url     : https://prove2.me/submissions/4da0e8a5-7adb-4e37-a610-3ecd89ffcd6f

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- At the original controlled predictable positive reserve, every
nonpositive spectrally negative Levy mark has a nonpositive w increment,
including exact landing at zero and ruin overshoots below zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (t : ℝ≥0)
    (hregion :
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C)
    (z : ℝ) (hz : z ≤ 0) :
    w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t + z) ≤
      w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) := by
  let y : ℝ := Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  change w (y + z) ≤ w y
  have hNonneg : 0 ≤ w y := by
    have hSec :=
      avram_wave3_03_bv_full_cap_gradient_secant
        C hC w hw_cont hw_smooth hw_grad
        0 y (le_refl (0 : ℝ)) (le_of_lt hregion.1)
        (le_of_lt hregion.2)
    have hSec' : y ≤ w y - w 0 := by simpa using hSec
    linarith
  by_cases hLand : 0 ≤ y + z
  · have hOrder : y + z ≤ y := by linarith
    have hSec :=
      avram_wave3_03_bv_full_cap_gradient_secant
        C hC w hw_cont hw_smooth hw_grad
        (y + z) y hLand hOrder (le_of_lt hregion.2)
    linarith
  · have hBelow : y + z < 0 := lt_of_not_ge hLand
    rw [hw_neg (y + z) hBelow]
    exact hNonneg
