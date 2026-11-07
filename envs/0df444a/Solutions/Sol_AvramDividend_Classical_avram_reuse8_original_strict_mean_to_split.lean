-- Prove2me | solution 1 for AvramDividend.Classical.avram_reuse8_original_strict_mean_to_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:25:07.829245+00:00
-- url     : https://prove2.me/submissions/884a55ff-a378-4e41-bbb0-d3522e20e6a0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_witness_from_strict_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let Strict : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
    (∫ ω, Strict ω ∂P) ≤ w x →
    ∃ M B : Ω → ℝ,
      (Integrable M P ∧ (∫ ω, M ω ∂P) = 0) ∧
      (Integrable B P ∧ (∫ ω, B ω ∂P) ≤ 0) ∧
      (∀ᵐ ω ∂P, Strict ω ≤ w x + M ω + B ω) := by
  dsimp
  intro hMean
  obtain ⟨E, hEI, hEmean, hEbound⟩ :=
    avram_p3_bv_original_source_witness_from_strict_mean
      X hBV x C D hD w hw_cont hw_neg q hq T hT hMean
  refine ⟨(fun ω => E ω - E ω), E, ?_, ?_, ?_⟩
  · constructor
    · exact hEI.sub hEI
    · rw [integral_sub hEI hEI]
      exact sub_self _
  · exact ⟨hEI, hEmean⟩
  · filter_upwards [hEbound] with ω hω
    simpa only [sub_self, add_zero] using hω
