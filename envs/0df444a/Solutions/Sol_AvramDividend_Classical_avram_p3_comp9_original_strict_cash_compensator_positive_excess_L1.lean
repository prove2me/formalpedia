-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp9_original_strict_cash_compensator_positive_excess_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:34:46.564541+00:00
-- url     : https://prove2.me/submissions/9e448117-6ec2-4c5e-8d44-81ec1f088816

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_canonical_strict_prefix_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
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
    (q : ℝ) (hq : 0 < q) (T : ℝ) (hT : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (M B : ℕ → Ω → ℝ)
    (hMI : ∀ n, Integrable (M n) P)
    (hBI : ∀ n, Integrable (B n) P) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)
    ∀ n, Integrable
      (fun ω => max (F n ω - (w x + (M n ω + B n ω))) 0) P := by
  dsimp only
  intro n
  letI : IsProbabilityMeasure P := X.isProbability
  have hF :=
    (avram_p3_comp8_original_canonical_strict_prefix_integrable
      X hBV x C D hD w hw_cont hw_neg q hq T hT hw_nonneg) n
  have hConst : Integrable (fun _ : Ω => w x) P := integrable_const (w x)
  have hSigned : Integrable (fun ω => w x + (M n ω + B n ω)) P :=
    hConst.add ((hMI n).add (hBI n))
  have hZero : Integrable (fun _ : Ω => (0 : ℝ)) P := integrable_const 0
  exact (hF.sub hSigned).sup hZero
