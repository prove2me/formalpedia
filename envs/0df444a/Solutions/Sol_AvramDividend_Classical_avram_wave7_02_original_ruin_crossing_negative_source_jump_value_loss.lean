-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_ruin_crossing_negative_source_jump_value_loss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:37:11.780283+00:00
-- url     : https://prove2.me/submissions/40d33a74-5ea4-4196-abc4-f409704581eb

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

/-- At a true original-source ruin-crossing jump, the candidate value loss
is nonpositive even though the postjump reserve lies outside its C1 band. -/
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
    (hb : 0 ≤ x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)
    (hbC : ENNReal.ofReal
      (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) ≤ C)
    (ha : x + X.X t ω - D t ω < 0) :
    X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t < 0 ∧
    w (x + X.X t ω - D t ω) -
      w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) ≤ 0 := by
  have hSource : X.X t ω - Function.leftLim
      (fun s : ℝ≥0 => X.X s ω) t < 0 := by
    linarith
  have hSec : (x + Function.leftLim
      (fun s : ℝ≥0 => X.X s ω) t - D t ω) - 0 ≤
      w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) -
        w 0 := by
    simpa using avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad
      0 (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)
      (le_refl (0 : ℝ)) hb hbC
  have hValueBefore : 0 ≤
      w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) := by
    linarith
  have hValueAfter : w (x + X.X t ω - D t ω) = 0 :=
    hw_neg _ ha
  constructor
  · exact hSource
  · rw [hValueAfter]
    linarith
