-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_stopped_cash_restrict_association
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:08:46.310337+00:00
-- url     : https://prove2.me/submissions/0fe26cd4-3cfd-487d-b23e-7ca27328bd2e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Associativity of physical original dividend-measure restriction:
first by actual payment times, then by one stopped mesh cell, yields
the exact intersection occurring in the canonical strict cash integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ≥0) (m i : ℕ) (f : ℝ → ℝ≥0∞) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (u i : ℝ) (u (i + 1) : ℝ),
      f t ∂(dividendMeasure D ω)) =
    (∫⁻ t in Ioc (u i : ℝ) (u (i + 1) : ℝ),
      f t ∂((dividendMeasure D ω).restrict
        (paymentTimes (ruinTime X x D ω)))) := by
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  let A : Set ℝ := Ioc (u i : ℝ) (u (i + 1) : ℝ)
  let B : Set ℝ := paymentTimes (ruinTime X x D ω)
  have hMeasure :
      ((dividendMeasure D ω).restrict B).restrict A =
        (dividendMeasure D ω).restrict (B ∩ A) := by
    calc
      ((dividendMeasure D ω).restrict B).restrict A =
          (dividendMeasure D ω).restrict (A ∩ B) :=
        Measure.restrict_restrict measurableSet_Ioc
      _ = (dividendMeasure D ω).restrict (B ∩ A) := by
        rw [inter_comm]
  change (∫⁻ t, f t ∂(dividendMeasure D ω).restrict (B ∩ A)) =
    (∫⁻ t, f t ∂((dividendMeasure D ω).restrict B).restrict A)
  rw [hMeasure]
