-- Prove2me | solution 1 for AvramDividend.Classical.chat04_future_killed_scale_payoff_terminal_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:19:47.432478+00:00
-- url     : https://prove2.me/submissions/7ef7798c-1b46-47da-ac92-b8e344d60abf

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_future_killing_terminal_filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-! The future killed q-scale payoff is measurable when the whole future
window has become observable at the terminal time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    Measurable[𝓕 u]
      (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
          0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
        (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
          W (x + X.X u ω))) := by
  have hXu : Measurable[𝓕 u] (X.X u) := X.adapted u
  have hWmeas : Measurable[𝓕 u]
      (fun ω => W (x + X.X u ω)) :=
    (chat03_scale_function_borel_measurable X q W hW).comp
      (measurable_const.add hXu)
  have hPay : Measurable[𝓕 u]
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω)) :=
    measurable_const.mul hWmeas
  exact hPay.indicator
    (chat04_shifted_future_killing_terminal_filtration X x s u hsu)
