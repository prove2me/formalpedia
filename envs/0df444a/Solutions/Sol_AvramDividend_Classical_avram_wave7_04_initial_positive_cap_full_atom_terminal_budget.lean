-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_04_initial_positive_cap_full_atom_terminal_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:43:47.960047+00:00
-- url     : https://prove2.me/submissions/1c79b2cd-c0e8-43a3-8ed3-4bafc87e3937

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_chronological_stopped_terminal_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave7_04_initial_full_atom_plus_survival_terminal_pathwise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (0 : ℝ≥0∞) < ruinTime X x D ω then
       max 0 (w (x - rightLimit D 0 ω))
     else 0) ≤ w x := by
  classical
  have hSmoothPair :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
    constructor
    · intro hContr
      exact False.elim (hContr hBV)
    · intro _
      exact hw_smooth
  have hPost : ∀ η : Ω, 0 ≤ w (x - rightLimit D 0 η) := by
    intro η
    have hValue :=
      avram_wave5_03_original_chronological_stopped_terminal_nonnegative
        X w C hC hw0 hw_cont hw_neg hSmoothPair hw_grad
        x hxc D hD η (0 : ℝ≥0)
    simpa [X.X_zero η] using hValue
  exact avram_wave7_04_initial_full_atom_plus_survival_terminal_pathwise
    X x q D hD.1.1 w hjump hPost ω
