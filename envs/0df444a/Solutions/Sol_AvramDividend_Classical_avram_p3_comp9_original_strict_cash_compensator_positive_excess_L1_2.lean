-- Prove2me | solution 2 for AvramDividend.Classical.avram_p3_comp9_original_strict_cash_compensator_positive_excess_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:36:05.310934+00:00
-- url     : https://prove2.me/submissions/d0c0c8e0-d835-4da2-a05e-9594a1b18fdf

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

/-! The Lévy structure supplies the probability-measure instance needed for
the integrability of a constant initial value. -/
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
  letI : IsProbabilityMeasure P := X.isProbability
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  change ∀ n, Integrable
    (fun ω => max (F n ω - (w x + (M n ω + B n ω))) 0) P
  intro n
  have hF : Integrable (F n) P :=
    avram_p3_comp8_original_canonical_strict_prefix_integrable
      X hBV x C D hD w hw_cont hw_neg q hq T hT hw_nonneg n
  have hW : Integrable (fun _ : Ω => w x) P := integrable_const _
  have hMB : Integrable (fun ω : Ω => M n ω + B n ω) P :=
    (hMI n).add (hBI n)
  have hDiff : Integrable
      (fun ω : Ω => F n ω - (w x + (M n ω + B n ω))) P := by
    exact hF.sub (hW.add hMB)
  exact hDiff.pos_part
