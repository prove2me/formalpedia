-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_cap_generator_and_secant_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:47:30.927162+00:00
-- url     : https://prove2.me/submissions/5188214c-118c-442a-9c1e-773c2e126e18

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_allcap_actual_generator_interior_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_source_generatorIntegrable_iff
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_source_generator_eq_interior
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_allCap_admissible_initial_capital_nonneg
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original controlled reserve may contact the cap, including at time zero.
Its dividend secants hold pathwise at every pre-ruin time, while its source
generator drift is nonpositive almost everywhere in physical time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_gen : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (μ : Measure ℝ≥0) [SFinite μ] :
    (∀ ω (t : ℝ≥0),
      (t : ℝ≥0∞) < ruinTime X x D ω →
      ∀ a : ℝ, 0 ≤ a → a ≤ riskProcess X x D t ω →
        riskProcess X x D t ω - a ≤
          w (riskProcess X x D t ω) - w a) ∧
    (∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
        X.GeneratorIntegrable
          (fun y => if y ≤ c then w y else w c + (y - c))
          (riskProcess X x D t ω) ∧
        X.generator
          (fun y => if y ≤ c then w y else w c + (y - c))
          (riskProcess X x D t ω) -
          q * (if riskProcess X x D t ω ≤ c then
            w (riskProcess X x D t ω)
          else w c + (riskProcess X x D t ω - c)) ≤ 0) := by
  have hC0 : ENNReal.ofReal c ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  have hx : 0 ≤ x :=
    avram_wave3_04_allCap_admissible_initial_capital_nonneg
      X x (ENNReal.ofReal c) hxc D hD
  constructor
  · intro ω t ht a ha hab
    have hRange :=
      capped_riskProcess_range_before_ruin_including_zero
        X x hx (ENNReal.ofReal c) hxc D hD ω t ht
    exact avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
      (ENNReal.ofReal c) w hw_cont hw_smooth hw_grad
      a (riskProcess X x D t ω) ha hab hRange.2
  · have hInside :=
      avram_wave4_04_ubv_allcap_actual_generator_interior_no_grid
        X hBV x (ENNReal.ofReal c) hC0 D hD hxc μ
    filter_upwards [hInside] with ω hω
    filter_upwards [hω] with t ht
    intro hpre
    have hState := ht hpre
    let u : ℝ := riskProcess X x D t ω
    have hu : 0 < u := hState.1
    have hucE : ENNReal.ofReal u < ENNReal.ofReal c := hState.2
    have huc : u < c :=
      (ENNReal.ofReal_lt_ofReal_iff hc).mp hucE
    have hHJB := hw_gen u hu hucE
    refine ⟨?_, ?_⟩
    · exact
        (avram_wave4_04_cap_linear_extension_source_generatorIntegrable_iff
          X w c u huc).2 hHJB.1
    · rw [avram_wave4_04_cap_linear_extension_source_generator_eq_interior
        X w c u huc]
      have hVal :
          (if riskProcess X x D t ω ≤ c then
            w (riskProcess X x D t ω)
          else w c + (riskProcess X x D t ω - c)) = w u := by
        exact if_pos (le_of_lt huc)
      rw [hVal]
      exact hHJB.2
