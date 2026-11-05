-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_assist_original_positive_compact_intensity_eq_nu_tests_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:41:28.511452+00:00
-- url     : https://prove2.me/submissions/56cd896d-5f0f-4d96-b17a-08fbe20704cc

import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_original_unit_tonelli_same_all_horizon_intensity_v2
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_original_finite_jump_test_count_integral_v2
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_nonnegative_compact_jump_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_test_support_separated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
/-- One original-process marked intensity has all-horizon count scaling and agrees with the genuine Lévy measure on separated compactly supported nonnegative continuous tests. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ σ : Measure ℝ,
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 T ×ˢ B) ∂P) =
          (T : ℝ≥0∞) * σ B) ∧
      (∀ (f : ℝ → ℝ) (hf : Continuous f)
          (hc : IsCompact (tsupport f))
          (hneg : tsupport f ⊆ Iio (0 : ℝ))
          (hfnonneg : ∀ y : ℝ, 0 ≤ f y),
        (∫⁻ y, ENNReal.ofReal (f y) ∂σ) =
          ENNReal.ofReal (∫ y, f y ∂(X.ν.restrict (Iio (0 : ℝ))))) ∧
      (∀ ε : ℝ, 0 < ε → σ (Iic (-ε)) < ⊤) ∧
      (∀ B : Set ℝ, MeasurableSet B →
        σ B = σ (B ∩ Iio (0 : ℝ))) ∧
      SigmaFinite σ := by
  obtain ⟨σ, hRate, hTonelli, hBand, hSupport, hSF⟩ := avram_p2_a_assist_original_unit_tonelli_same_all_horizon_intensity_v2 X
  refine ⟨σ, hRate, ?_, hBand, hSupport, hSF⟩
  intro f hf hc hneg hfnonneg
  obtain ⟨ε, hε, hSupp⟩ := avram_p2_a_zero_rate_compact_negative_test_support_separated f hf hc hneg
  have hfzero : f 0 = 0 := by
    by_contra hn
    have h0 : (0 : ℝ) ∈ Function.support f := hn
    have hle : (0 : ℝ) ≤ -ε := hSupp h0
    linarith
  obtain ⟨J, hJ, hJump, hJNonneg, hMean⟩ := avram_p2_a_zero_rate_original_nonnegative_compact_jump_lintegral P X (1 : ℝ≥0) (by norm_num) f hf hc hneg hfnonneg
  have hInner (ω : Ω) :
      (∫⁻ p in (Ioc 0 (1 : ℝ≥0) ×ˢ (Set.univ : Set ℝ)),
        ENNReal.ofReal (f p.2) ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
        ENNReal.ofReal (J ω) := by
    obtain ⟨F, hF, hSum⟩ := hJump ω
    have hFactual (u : ℝ≥0) :
        u ∈ F ↔
          (0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
          u ∈ Ioc 0 (1 : ℝ≥0) ∧
          f (X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0 := by
      constructor
      · intro hu
        rcases (hF u).1 hu with ⟨hpos, hle, hfnz⟩
        refine ⟨⟨hpos, ?_⟩, ⟨hpos, hle⟩, hfnz⟩
        intro hΔ
        apply hfnz
        simpa [hΔ] using hfzero
      · rintro ⟨⟨hpos, _⟩, ⟨_, hle⟩, hfnz⟩
        exact (hF u).2 ⟨hpos, hle, hfnz⟩
    have hCount := avram_p2_a_assist_original_finite_jump_test_count_integral_v2 X ω (1 : ℝ≥0) f hf.measurable hfnonneg F hFactual
    simpa [hSum] using hCount
  have hBridge :
      (∫⁻ ω, ∫⁻ p in (Ioc 0 (1 : ℝ≥0) ×ˢ (Set.univ : Set ℝ)),
        ENNReal.ofReal (f p.2) ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) =
        (∫⁻ ω, ENNReal.ofReal (J ω) ∂P) := by
    apply lintegral_congr_ae
    filter_upwards [] with ω
    exact hInner ω
  simpa using (hTonelli f hf.measurable).trans (hBridge.trans hMean)
