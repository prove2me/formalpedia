-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_compact_HJB_from_global_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:54:10.38649+00:00
-- url     : https://prove2.me/submissions/dee11577-fd9a-48c0-80f8-1eb6a08774d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_compact_prestate_HJB_expected_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The canonical interior HJB inequality controls the exact original
BV generator drift on any compact positive reserve strip below the cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞) (T : ℝ≥0)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (a b : ℝ) (ha : 0 < a) (hbC : ENNReal.ofReal b < C)
    (Upre : ℝ≥0 × Ω → ℝ)
    (hUpre : ∀ p, Upre p = Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
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
  have hlocal (p : ℝ≥0 × Ω) (hp : Upre p ∈ Icc a b) :
      X.GeneratorIntegrable w (Upre p) ∧
        X.generator w (Upre p) - q * w (Upre p) ≤ 0 := by
    have hpos : 0 < Upre p := lt_of_lt_of_le ha hp.1
    have hcap : ENNReal.ofReal (Upre p) < C :=
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hp.2) hbC
    exact hw_gen (Upre p) hpos hcap
  exact avram_p3_bv_original_compact_prestate_HJB_expected_nonpos
    X hBV x D hD w q T a b Upre hUpre
    (by intro p hp; exact (hlocal p hp).1)
    (by intro p hp; exact (hlocal p hp).2)
    F hF hFint
