-- Prove2me | solution 1 for AvramDividend.Classical.chat03_killed_scale_payoff_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T10:54:07.468033+00:00
-- url     : https://prove2.me/submissions/463cceaa-db6e-410d-b76e-a32dc49b4c78

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_lower_survival_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
The full-path downward-killed discounted q-scale process is adapted.
This is a necessary analytic input for the still-open killed martingale
identity, and uses a genuine one-sided survival history.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Adapted 𝓕
      (fun (t : ℝ≥0) ω =>
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp (-(q * (t : ℝ))) *
            W (x + X.X t ω)) ω) := by
  intro t
  have hEquiv :
      {ω : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω} =
      {ω : Ω | ∀ s : ℝ≥0, s ≤ t → ¬ X.X s ω < -x} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h s hs hBad
      have hNonneg := h s hs
      linarith
    · intro h s hs
      have hn := h s hs
      have hBound : -x ≤ X.X s ω := le_of_not_gt hn
      linarith
  have hSurv : MeasurableSet[𝓕 t]
      {ω : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω} := by
    rw [hEquiv]
    exact chat03_lower_survival_filtration_measurable
      X τ hCover (-x) t
  have hXt : Measurable[𝓕 t] (X.X t) := X.adapted t
  have hWm : Measurable W :=
    chat03_scale_function_borel_measurable X q W hW
  have hPay : Measurable[𝓕 t]
      (fun ω : Ω => Real.exp (-(q * (t : ℝ))) *
        W (x + X.X t ω)) := by
    exact measurable_const.mul
      (hWm.comp (measurable_const.add hXt))
  exact hPay.indicator hSurv
