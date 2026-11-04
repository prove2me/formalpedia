-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_exact_clock_inclusive_strict_integrable_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:24:21.873448+00:00
-- url     : https://prove2.me/submissions/11c0d069-0124-48bd-aab3-8aae3e1c5483

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_clock_inclusive_strict_ae_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Exact original inclusive and strict physical clock integrability coincide. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (μ : Measure ℝ≥0) [NullSingletonClass μ]
    (f : ℝ≥0 → ℝ) (ω : Ω) :
    Integrable (fun t : ℝ≥0 => if t ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal then f t else 0) μ ↔
    Integrable (fun t : ℝ≥0 => if 0 < t ∧ t < (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal then f t else 0) μ := by
  have hAE :=
    (avram_p4_e_localise_original_exact_clock_inclusive_strict_ae_integral
      X x D n μ f ω).1
  constructor
  · intro h
    exact h.congr hAE
  · intro h
    exact h.congr hAE.symm
