-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_positive_time_ae_budget_suffices_all_ubv_horizons
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:41:42.451302+00:00
-- url     : https://prove2.me/submissions/049a8251-4fdf-4640-bee9-f57319836c95

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_zero_horizon_hjb_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_source_ubv_value_from_ae_future_clock_budget
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The stochastic source-clock budget is needed only when the horizon and
    initial capital are strictly positive; the genuine time-zero atom is
    already controlled by the source HJB secant. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hPositiveClocks : ∀ T : ℝ, 0 < T → 0 < x →
      ∃ η : Ω → ℝ≥0∞,
        (∀ᵐ ω ∂P, ENNReal.ofReal T < η ω) ∧
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (η ω)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) :
    ∀ T : ℝ, 0 ≤ T →
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) := by
  have hsmooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :=
    ⟨fun _ => hw_smooth, fun hbv => (hBV hbv).elim⟩
  intro T hT
  rcases eq_or_lt_of_le hT with hzero | hTpos
  · have ht0 : T = 0 := hzero.symm
    subst T
    exact admissible_cap_truncated_zero_horizon_hjb_bound
      X q x w C hw_cont hw0 hsmooth hw_hjb D hD hxc
  · exact avram_wave7_11_source_ubv_value_from_ae_future_clock_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_hjb x hx hxc D hD T (le_of_lt hTpos)
      (fun hxpos => hPositiveClocks T hTpos hxpos)
