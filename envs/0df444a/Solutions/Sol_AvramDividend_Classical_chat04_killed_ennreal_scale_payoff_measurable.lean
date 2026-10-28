-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_ennreal_scale_payoff_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:13:55.543+00:00
-- url     : https://prove2.me/submissions/bf4c244c-e7d0-4e2f-889c-47a1573891d9

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_lower_survival_closed_window_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The continuously downward-killed discounted q-scale payoff is
measurable as an extended nonnegative reward at each finite horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) :
    Measurable (fun ω : Ω =>
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω) := by
  have hEquiv :
      {u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u} =
      {u : Ω | ∀ s : ℝ≥0, (0 : ℝ≥0) ≤ s → s ≤ t →
        ¬ X.X s u < -x} := by
    ext u
    simp only [mem_setOf_eq]
    constructor
    · intro h s _ hst hBad
      have hs := h s hst
      linarith
    · intro h s hst
      have hs := h s bot_le hst
      have hb : -x ≤ X.X s u := le_of_not_gt hs
      linarith
  have hSurv : MeasurableSet
      {u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u} := by
    rw [hEquiv]
    exact chat04_lower_survival_closed_window_measurable
      X (-x) 0 t bot_le
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hWm : Measurable W :=
    chat03_scale_function_borel_measurable X q W hW
  have hPay : Measurable (fun u : Ω =>
      Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) :=
    measurable_const.mul (hWm.comp (measurable_const.add hXt))
  have hPayENN : Measurable (fun u : Ω =>
      ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) :=
    ENNReal.continuous_ofReal.measurable.comp hPay
  exact hPayENN.indicator hSurv
