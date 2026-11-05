-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_source_witness_from_strict_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:37:38.023294+00:00
-- url     : https://prove2.me/submissions/27ef47c0-2116-4caa-b16a-a7c7155aa379

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The original source has probability mass one in its own structure.
The actual strict payoff minus its initial value is consequently an L1
signed residual witness whenever its physical expected budget holds. -/
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
    ∃ E : Ω → ℝ, Integrable E P ∧
      (∫ ω, E ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P, Strict ω ≤ w x + E ω) := by
  intro S Strict hMean
  letI : IsProbabilityMeasure P := X.isProbability
  have hInt : Integrable Strict P :=
    avram_p3_bv_original_prebudget_L1
      X hBV x C D hD w hw_cont hw_neg q hq T hT
  refine ⟨fun ω => Strict ω - w x, hInt.sub (integrable_const _), ?_, ?_⟩
  · have hE : (∫ ω, Strict ω - w x ∂P) =
        (∫ ω, Strict ω ∂P) - w x := by
      rw [integral_sub hInt (integrable_const _)]
      simp
    rw [hE]
    exact sub_nonpos.mpr hMean
  · filter_upwards [] with ω
    exact le_of_eq (by ring)
