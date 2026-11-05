-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_compact_prestate_HJB_expected_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:45:57.413196+00:00
-- url     : https://prove2.me/submissions/9b388a7a-372d-4a0c-ab6f-3d140ffd8e2f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_true_clock_signed_HJB_expected_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual controlled pre-jump reserve compact band is predictable, so the
original BV Lévy signed HJB drift has nonpositive finite-time expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0) (a b : ℝ)
    (Upre : ℝ≥0 × Ω → ℝ)
    (hUpre : ∀ p, Upre p = Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
    (hGen : ∀ p, Upre p ∈ Icc a b → X.GeneratorIntegrable w (Upre p))
    (hHJB : ∀ p, Upre p ∈ Icc a b →
      X.generator w (Upre p) - q * w (Upre p) ≤ 0)
    (F : ℝ≥0 × Ω → ℝ)
    (hF : ∀ p, F p = if Upre p ∈ Icc a b then
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift * deriv w (Upre p) +
          (∫ z in Iio (0 : ℝ), w (Upre p + z) - w (Upre p) ∂X.ν) -
          q * w (Upre p)) else 0)
    (hFint : Integrable F
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal).prod P)) :
    (∫ p, F p ∂((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal).prod P)) ≤ 0 := by
  classical
  let E : Set (ℝ≥0 × Ω) := {p | Upre p ∈ Icc a b}
  have hEeq : E = {p | Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b} := by
    ext p
    change (Upre p ∈ Icc a b) ↔ (_ ∈ Icc a b)
    rw [hUpre p]
  have hEm : MeasurableSet[𝓕.rightCont.predictable] E := by
    rw [hEeq]
    exact avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
      X x D hD a b
  exact avram_p3_b_bvjump_original_controlled_true_clock_signed_HJB_expected_nonpos
    X hBV D hD x w q T Upre hUpre E hEm
    (by intro p hp; exact hGen p hp)
    (by intro p hp; exact hHJB p hp)
    F (by intro p; simpa only [E, Set.mem_setOf_eq] using hF p) hFint
