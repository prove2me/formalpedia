-- Prove2me | solution 1 for AvramDividend.Classical.chat04_standing_future_window_killed_scale_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:05:34.641349+00:00
-- url     : https://prove2.me/submissions/b6f76099-c47b-4ad5-a5ed-8efc2ab4c6db

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_future_window_killed_scale_integrable_of_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_lower_survival_closed_window_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-! The future-window killed q-scale payoff is integrable with no
auxiliary measurability or moment assumptions beyond Standing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    Integrable
      (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
        (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
          W (x + X.X u ω))) P := by
  let B : Set Ω :=
    {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}
  let C : Set Ω :=
    {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u → ¬ X.X v ω < -x}
  have hEq : B = C := by
    ext ω
    change (∀ v : ℝ≥0, s ≤ v → v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)) ↔
      (∀ v : ℝ≥0, s ≤ v → v ≤ u → ¬ X.X v ω < -x)
    constructor
    · intro h v hsv hvu
      have hv := h v hsv hvu
      have hle : -x ≤ X.X v ω := by linarith
      exact not_lt.mpr hle
    · intro h v hsv hvu
      have hv : -x ≤ X.X v ω := not_lt.mp (h v hsv hvu)
      linarith
  have hB : MeasurableSet B := by
    rw [hEq]
    exact chat04_lower_survival_closed_window_measurable
      X (-x) s u hsu
  exact chat04_future_window_killed_scale_integrable_of_measurable
    X hX q hq W hW x s u hsu hB
