-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_BV_capped_ruin_clock_terminal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:11:19.524218+00:00
-- url     : https://prove2.me/submissions/ac7ac71a-e541-4bf0-8abf-113483824973

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_deterministic_bounded_ruin_stopping_package
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_random_stop_survival_terminal_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original finite ruin clock inherits stopped-survival terminal integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    Integrable (fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) P := by
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
  have hpackage :=
    avram_wave6_ubv_original_deterministic_bounded_ruin_stopping_package
      X x C D hD
  have hfinite (ω : Ω) :
      min (ruinTime X x D ω) (n : ℝ≥0∞) < ⊤ :=
    lt_of_le_of_lt (hpackage.2.1 n ω) ENNReal.coe_lt_top
  have hτco (ω : Ω) : (τ ω : ℝ≥0∞) =
      min (ruinTime X x D ω) (n : ℝ≥0∞) :=
    ENNReal.coe_toNNReal (ne_of_lt (hfinite ω))
  have hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) := by
    have heq : (fun ω => (τ ω : ℝ≥0∞)) =
        (fun ω => min (ruinTime X x D ω) (n : ℝ≥0∞)) := by
      funext ω
      exact hτco ω
    change IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : ℝ≥0∞))
    rw [heq]
    exact hpackage.1 n
  have hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0) := by
    intro ω
    have hBoundE : (τ ω : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
      rw [hτco ω]
      exact hpackage.2.1 n ω
    exact_mod_cast hBoundE
  exact avram_wave8_20_original_BV_bounded_random_stop_survival_terminal_integrable
    X hX hBV q hq w hw_cont hw_neg x C D hD n τ hτstop hτbound
