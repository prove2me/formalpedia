-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_uniform_capped_generator_expected_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:59:54.82626+00:00
-- url     : https://prove2.me/submissions/110e5daf-2991-49a3-ae5f-5f6a6ad31c7a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_joint_measurable_max_HJB_capped_expected_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_max_HJB_exact_physical_generator_sign
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_capped_HJB_time_envelope_expected_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_time_enveloped_HJB_generator_nonpos_expectation
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_capped_HJB_implies_K_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_time_enveloped_generator_L1_and_Fubini
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_stopped_generator_L1_nonpos_mean
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Original stopped physical HJB generator has nonpositive expected drift when its true predictable product is dominated by an integrable time envelope. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
  (T : ℝ≥0) (μT : Measure ℝ≥0) [SFinite μT]
  (hTime : μT = (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
  (A : Ω → Set ℝ≥0) (hAm : ∀ ω, MeasurableSet (A ω))
  (K : ℝ≥0 → Ω → ℝ)
  (hK : ∀ t ω, K t ω =
    Real.exp (-(q * (t : ℝ))) *
      (X.drift * deriv w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) +
      (∫ z in Iio (0 : ℝ),
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t + z) -
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t) ∂X.ν) -
      q * w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t)))
  (F : (ℝ≥0 × Ω) → ℝ)
  (hF : ∀ p, F p = if p.1 ∈ A p.2 then K p.1 p.2 else 0)
  (hASet : MeasurableSet {p : ℝ≥0 × Ω | p.1 ∈ A p.2})
  (hKmeas : Measurable (fun p : ℝ≥0 × Ω => K p.1 p.2))
  (B : ℝ) (hBnonneg : 0 ≤ B) (hμfinite : μT Set.univ < ∞)
  (hUniform : ∀ᵐ p ∂(μT.prod P), ‖F p‖ ≤ B)
  (Gdrift : Ω → ℝ)
  (hGDef : ∀ᵐ ω ∂P, Gdrift ω = ∫ t in A ω, K t ω ∂μT)
  (C : ℝ≥0∞)
  (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.GeneratorIntegrable w y ∧
    max (X.generator w y - q * w y) (1 - deriv w y) = 0)
  (hRegion : ∀ᵐ ω ∂P, ∀ t, t ∈ A ω →
    0 < Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
    ENNReal.ofReal (Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C) :
  Integrable Gdrift P ∧
  (∀ᵐ ω ∂P, Gdrift ω ≤ 0) ∧
  (∫ ω, Gdrift ω ∂P) ≤ 0 := by

  haveI : IsFiniteMeasure μT := ⟨hμfinite⟩
  have hgI : Integrable (fun _ : ℝ≥0 => B) μT := integrable_const B
  have hFbound : ∀ᵐ p ∂(μT.prod P),
      ‖F p‖ ≤ ‖(fun _ : ℝ≥0 => B) p.1‖ := by
    filter_upwards [hUniform] with p hp
    simpa [Real.norm_eq_abs, abs_of_nonneg hBnonneg] using hp
  exact avram_wave8_22_original_BV_joint_measurable_max_HJB_capped_expected_nonpos
    X hBV q w x D T μT hTime A hAm K hK F hF hASet hKmeas
    (fun _ => B) hgI hFbound Gdrift hGDef C hw_hjb hRegion
