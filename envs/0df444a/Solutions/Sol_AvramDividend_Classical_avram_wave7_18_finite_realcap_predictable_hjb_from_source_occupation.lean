-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_finite_realcap_predictable_hjb_from_source_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:41:49.942828+00:00
-- url     : https://prove2.me/submissions/159fb139-ce0e-435d-a3d9-efa2ca86c099

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_predictable_positive_before_localiser_all_caps
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_strict_subcap_ae_on_atomless_clock

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q c : ℝ) (hc : 0 < c) (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal c →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal c →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hCap : ∀ ω (s : ℝ≥0), (s : ℝ≥0∞) < ruinTime X x D ω →
      riskProcess X x D s ω ≤ c)
    (σ : Ω → ℝ≥0∞) (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < σ ω) →
      let y : ℝ := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      (0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c) ∧
        ContDiffWithinAt ℝ 2 w
          {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c} y ∧
        X.GeneratorIntegrable w y ∧
        X.generator w y - q * w y ≤ 0 ∧ 1 ≤ deriv w y := by
  have hpos :=
    avram_wave5_ubv_original_predictable_positive_before_localiser_all_caps
      X hBV x (ENNReal.ofReal c) D hD σ hσ μ
  have hsub :=
    avram_wave5_05_ubv_original_predictable_strict_subcap_ae_on_atomless_clock
      X hBV x c D hD.1.1 hCap μ
  filter_upwards [hpos, hsub] with ω hω hcω
  filter_upwards [hω, hcω] with t ht hc_t
  intro htBefore
  dsimp
  have hy : 0 < Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t :=
    ht htBefore
  have hyc : Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t < c :=
    hc_t htBefore.1 (lt_of_lt_of_le htBefore.2 (hσ ω))
  have hcap' : ENNReal.ofReal (Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < ENNReal.ofReal c :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hy)).2 hyc
  exact ⟨⟨hy, hcap'⟩, hw_smooth _ ⟨hy, hcap'⟩,
    (hw_gen _ hy hcap').1, (hw_gen _ hy hcap').2, hw_grad _ hy hcap'⟩
