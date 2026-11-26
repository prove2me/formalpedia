-- Prove2me | solution 27 for AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_unbounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:52:58.512803+00:00
-- url     : https://prove2.me/submissions/ca7edbba-1fcc-40a2-ab38-888d15a4ce29
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_positive_band_clock_certificate
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

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
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by 
  by_cases hz : x = 0
  · subst x
    have hs := local_verification_stochastic_core_side_conditions
      X q w C hw_cont hw0 ⟨fun _ => hw_smooth, fun hv => (hBV hv).elim⟩
      hw_hjb 0 hxc D hD
    exact avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
      X hBV q w C hw0 hw_cont hw_smooth hs.2.1 D hD hs.2.2.2 T hT
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
    apply ENNReal.le_of_forall_pos_le_add
    intro η hη _
    have hηreal : 0 < (η : ℝ) := hη
    obtain ⟨δ, R, θ, hband, hd, hR, hθle, hprefix, hstop, hm, hlim, hb⟩ :=
      avram_locmoll_positive_band_clock_certificate
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_hjb x hxpos hxc D hD T hT (η : ℝ) hηreal
    let F : ℕ → Ω → ℝ≥0∞ := fun k ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
    let V : Ω → ℝ≥0∞ := fun ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
    change (∫⁻ ω, V ω ∂P) ≤ _
    have heq : ∀ᵐ ω ∂P, V ω = liminf (fun k => F k ω) atTop := by
      filter_upwards [hlim] with ω hω
      exact hω.liminf_eq.symm
    calc
      (∫⁻ ω, V ω ∂P) ≤ liminf (fun k => ∫⁻ ω, F k ω ∂P) atTop := by
        rw [lintegral_congr_ae heq]
        exact lintegral_liminf_le' hm
      _ ≤ ENNReal.ofReal (w x + (η : ℝ)) :=
        Filter.liminf_le_of_frequently_le (Filter.Eventually.of_forall hb).frequently
      _ ≤ ENNReal.ofReal (w x) + η := by
        have h : ENNReal.ofReal (w x + (η : ℝ)) ≤
            ENNReal.ofReal (w x) + ENNReal.ofReal (η : ℝ) :=
          ENNReal.ofReal_add_le
        simpa using h
