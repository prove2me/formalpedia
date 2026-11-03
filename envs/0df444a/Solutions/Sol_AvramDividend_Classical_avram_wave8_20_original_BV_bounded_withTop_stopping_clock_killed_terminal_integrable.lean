-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_BV_bounded_withTop_stopping_clock_killed_terminal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:01:38.610423+00:00
-- url     : https://prove2.me/submissions/a94e071f-20b5-4dce-ba8f-4d70077a8fe5

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_random_stop_survival_terminal_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Finite WithTop stopping clocks retain exact killed terminal L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (σ : Ω → ℝ≥0∞)
    (hσStop : IsStoppingTime 𝓕.rightCont σ)
    (hσBound : ∀ ω, σ ω ≤ (H : ℝ≥0∞)) :
    let τ : Ω → ℝ≥0 := fun ω => (σ ω).toNNReal
    Integrable (fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) P := by
  classical
  let τ : Ω → ℝ≥0 := fun ω => (σ ω).toNNReal
  have hFinite (ω : Ω) : σ ω ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (hσBound ω)
  have hCoe (ω : Ω) : (τ ω : ℝ≥0∞) = σ ω := by
    dsimp [τ]
    exact ENNReal.coe_toNNReal (hFinite ω)
  have hτStop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) := by
    have hEq : (fun ω : Ω => (τ ω : WithTop ℝ≥0)) = σ := by
      funext ω
      exact hCoe ω
    rw [hEq]
    exact hσStop
  have hτBound (ω : Ω) : τ ω ≤ H := by
    apply ENNReal.coe_le_coe.mp
    rw [hCoe ω]
    exact hσBound ω
  change Integrable (fun ω =>
    if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * (τ ω : ℝ))) *
        w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
    else 0) P
  exact avram_wave8_20_original_BV_bounded_random_stop_survival_terminal_integrable
    X hX hBV q hq w hw_cont hw_neg x C D hD H τ hτStop hτBound
