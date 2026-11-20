-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_caplinear_discounted_terminal_continuous_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:27:24.17355+00:00
-- url     : https://prove2.me/submissions/12df02e7-b914-43fe-9da3-f1ec711a1d7f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_allcap_caplinear_continuousOn_nonnegative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0)) (C : ℝ≥0∞)
    (q : ℝ) (a : ℕ → ℝ≥0) (s : ℝ≥0)
    (ha : Tendsto a atTop (𝓝 s))
    (Y : ℕ → ℝ) (y : ℝ)
    (hY : Tendsto Y atTop (𝓝 y)) (hy : 0 ≤ y)
    (hYpos : ∀ᶠ m : ℕ in atTop, 0 ≤ Y m) :
    Tendsto (fun m =>
      Real.exp (-(q * (a m : ℝ))) *
        (if ENNReal.ofReal (Y m) ≤ C then w (Y m)
         else w C.toReal + (Y m - C.toReal)))
      atTop (𝓝 (Real.exp (-(q * (s : ℝ))) *
        (if ENNReal.ofReal y ≤ C then w y
         else w C.toReal + (y - C.toReal)))) := by
  let V : ℝ → ℝ := fun z =>
    if ENNReal.ofReal z ≤ C then w z else w C.toReal + (z - C.toReal)
  have hVcont : ContinuousOn V (Ici 0) :=
    avram_f6_original_allcap_caplinear_continuousOn_nonnegative w hw C
  have hwithin : Tendsto Y atTop (𝓝[Ici (0 : ℝ)] y) :=
    tendsto_nhdsWithin_iff.mpr ⟨hY, hYpos⟩
  have hV : Tendsto (fun m => V (Y m)) atTop (𝓝 (V y)) := by
    simpa only [Function.comp_def] using (hVcont y hy).tendsto.comp hwithin
  have htime : Tendsto (fun m => (a m : ℝ)) atTop (𝓝 (s : ℝ)) :=
    NNReal.tendsto_coe.mpr ha
  have hc : Continuous (fun t : ℝ => Real.exp (-(q * t))) := by fun_prop
  have hd : Tendsto (fun m => Real.exp (-(q * (a m : ℝ))))
      atTop (𝓝 (Real.exp (-(q * (s : ℝ))))) := by
    simpa only [Function.comp_def] using hc.continuousAt.tendsto.comp htime
  simpa only [V] using hd.mul hV
