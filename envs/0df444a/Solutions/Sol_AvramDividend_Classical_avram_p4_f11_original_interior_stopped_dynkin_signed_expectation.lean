-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f11_original_interior_stopped_dynkin_signed_expectation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:06:45.075957+00:00
-- url     : https://prove2.me/submissions/7bbe8f82-e5d8-496c-9346-dd176da96501
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_original_interior_physical_stopped_ito_meyer_martingale
import Theorems.Thm_AvramDividend_Classical_avram_p4_f9_original_finite_stopped_payoff_integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤) :
    ∀ (b : ℝ) (n : ℕ), 1 < b → 0 < n →
      let τ : Ω → ℝ≥0∞ := fun ω =>
        min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
      ∃ R : Ω → ℝ,
        Integrable R P ∧
        (∀ ω : Ω, R ω =
          (∫ s : ℝ in Icc (0 : ℝ) (n : ℝ),
            if ENNReal.ofReal s < τ ω ∧
              0 < 1 + X.X (Real.toNNReal s) ω ∧
              ENNReal.ofReal (1 + X.X (Real.toNNReal s) ω) < C then
              Real.exp (-(q * s)) *
                (X.generator w (1 + X.X (Real.toNNReal s) ω) -
                  q * w (1 + X.X (Real.toNNReal s) ω))
            else 0)) ∧
        (∫ ω, Real.exp (-(q * ENNReal.toReal (τ ω))) *
            w (1 + X.X (ENNReal.toNNReal (τ ω)) ω) ∂P) ≤
          w 1 + ∫ ω, R ω ∂P := by
  intro b n hb hn
  let τ : Ω → ℝ≥0∞ := fun ω =>
    min (twoSidedExitUpTimeCorrected X (b - 1) ω)
      (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
  obtain ⟨R, M, hRI, hMI, hRdef, hMzero, hIto⟩ :=
    AvramDividend.Classical.avram_p4_f11_original_interior_physical_stopped_ito_meyer_martingale X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad hTop b n hb hn
  have hTermI : Integrable (fun ω : Ω =>
      Real.exp (-(q * ENNReal.toReal (τ ω))) *
        w (1 + X.X (ENNReal.toNNReal (τ ω)) ω)) P := by
    simpa [τ] using AvramDividend.Classical.avram_p4_f9_original_finite_stopped_payoff_integrable X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad hTop b n (le_of_lt hb)
  letI : IsProbabilityMeasure P := X.isProbability
  have hBaseI : Integrable (fun ω : Ω => w 1 + M ω) P :=
    (integrable_const (w 1)).add hMI
  have hRightI : Integrable (fun ω : Ω => w 1 + M ω + R ω) P :=
    hBaseI.add hRI
  have hBudget : (∫ ω, Real.exp (-(q * ENNReal.toReal (τ ω))) *
      w (1 + X.X (ENNReal.toNNReal (τ ω)) ω) ∂P) ≤
      w 1 + ∫ ω, R ω ∂P := by
    calc
      _ ≤ ∫ ω, w 1 + M ω + R ω ∂P :=
        integral_mono_ae hTermI hRightI hIto
      _ = (∫ ω, w 1 + M ω ∂P) + (∫ ω, R ω ∂P) :=
        integral_add hBaseI hRI
      _ = w 1 + (∫ ω, R ω ∂P) := by
        rw [integral_add (integrable_const (w 1)) hMI]
        simp [hMzero]
  exact ⟨R, hRI, hRdef, hBudget⟩
