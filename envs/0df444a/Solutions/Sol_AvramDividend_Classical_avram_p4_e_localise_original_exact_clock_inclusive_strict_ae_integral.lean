-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_exact_clock_inclusive_strict_ae_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:14:16.961721+00:00
-- url     : https://prove2.me/submissions/720d47f6-47aa-4543-8d68-c92462511208

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Original ruin-truncated clock endpoints have zero physical-time measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (μ : Measure ℝ≥0) [NullSingletonClass μ]
    (f : ℝ≥0 → ℝ) (ω : Ω) :
    (fun t : ℝ≥0 => if t ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal then f t else 0)
      =ᵐ[μ] (fun t : ℝ≥0 => if 0 < t ∧ t < (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal then f t else 0) ∧
    (∫ t : ℝ≥0, if t ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal then f t else 0 ∂μ) =
      (∫ t : ℝ≥0, if 0 < t ∧ t < (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal then f t else 0 ∂μ) := by
  have hAE :
      (fun t : ℝ≥0 => if t ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal then f t else 0)
        =ᵐ[μ] (fun t : ℝ≥0 => if 0 < t ∧ t < (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal then f t else 0) := by
    filter_upwards [μ.ae_ne (0 : ℝ≥0), μ.ae_ne (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal]
      with s hsZero hsEnd
    have hsPos : 0 < s :=
      lt_of_le_of_ne (show (0 : ℝ≥0) ≤ s from zero_le) (Ne.symm hsZero)
    have hiff : s ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ↔
        0 < s ∧ s < (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := by
      constructor
      · intro hle
        exact ⟨hsPos, lt_of_le_of_ne hle hsEnd⟩
      · intro hs
        exact le_of_lt hs.2
    simp only [hiff]
  exact ⟨hAE, integral_congr_ae hAE⟩
