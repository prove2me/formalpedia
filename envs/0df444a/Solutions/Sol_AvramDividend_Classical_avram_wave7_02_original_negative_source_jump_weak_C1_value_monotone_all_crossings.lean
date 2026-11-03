-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_negative_source_jump_weak_C1_value_monotone_all_crossings
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:40:04.13017+00:00
-- url     : https://prove2.me/submissions/07ec5787-07ba-4668-8ca0-2c00e98c9b97

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

/-- The HJB gradient makes the original candidate nondecreasing across
every nonpositive source jump, including zero landing and ruin overshoot. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0)
    (hMark : X.X t ω ≤ Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)
    (hb : 0 ≤ x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)
    (hbC : ENNReal.ofReal
      (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) ≤ C) :
    w (x + X.X t ω - D t ω) ≤
      w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) := by
  have hOrder : x + X.X t ω - D t ω ≤
      x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω := by
    linarith
  by_cases ha : 0 ≤ x + X.X t ω - D t ω
  · have hSec : (x + Function.leftLim
        (fun s : ℝ≥0 => X.X s ω) t - D t ω) -
        (x + X.X t ω - D t ω) ≤
        w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) -
          w (x + X.X t ω - D t ω) := by
      exact avram_wave3_03_bv_full_cap_gradient_secant
        C hC w hw_cont hw_smooth hw_grad
        (x + X.X t ω - D t ω)
        (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)
        ha hOrder hbC
    linarith
  · have haNeg : x + X.X t ω - D t ω < 0 := lt_of_not_ge ha
    have hSec0 : (x + Function.leftLim
        (fun s : ℝ≥0 => X.X s ω) t - D t ω) - 0 ≤
        w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) -
          w 0 := by
      simpa using avram_wave3_03_bv_full_cap_gradient_secant
        C hC w hw_cont hw_smooth hw_grad
        0 (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)
        (le_refl (0 : ℝ)) hb hbC
    rw [hw_neg _ haNeg]
    linarith
