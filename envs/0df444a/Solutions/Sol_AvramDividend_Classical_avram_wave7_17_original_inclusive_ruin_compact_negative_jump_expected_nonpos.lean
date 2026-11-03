-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_inclusive_ruin_compact_negative_jump_expected_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:51:32.442429+00:00
-- url     : https://prove2.me/submissions/4a10a4da-3e59-4903-a3ea-9de5b0d57ac9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_compact_actual_negative_jump_expected_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_inclusive_ruin_predictable_strict_hjb_interior
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

/-- The concrete original ruin-inclusive compact predictable HJB band
has a nonpositive expected nonlinear source jump compensator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (q x : ℝ) (hq : 0 ≤ q) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
    (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (hCapBand : Icc a b ⊆
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hMass : X.ν (Iic (-a / 2)) < ⊤) :
    let E : Set (ℝ≥0 × Ω) := {p |
      ((p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
        0 < Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
        ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1) < C) ∧
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0
    Integrable (fun ω => ∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P ∧
    (∫ ω, (∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) ∂P) ≤ 0 := by
  let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
    Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t
  let E : Set (ℝ≥0 × Ω) := {p |
    ((p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
      0 < Y p.1 p.2 ∧ ENNReal.ofReal (Y p.1 p.2) < C) ∧
    Y p.1 p.2 ∈ Icc a b}
  have hYpred : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => Y p.1 p.2) :=
    (avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
      X x D hD).measurable
  have hBand : MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω | Y p.1 p.2 ∈ Icc a b} :=
    hYpred measurableSet_Icc
  have hInterior : MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
        0 < Y p.1 p.2 ∧ ENNReal.ofReal (Y p.1 p.2) < C} := by
    simpa only [Y] using
      avram_wave7_17_original_inclusive_ruin_predictable_strict_hjb_interior
        X x D hD C
  have hEm : MeasurableSet[𝓕.rightCont.predictable] E := by
    change MeasurableSet[𝓕.rightCont.predictable]
      ({p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
        0 < Y p.1 p.2 ∧ ENNReal.ofReal (Y p.1 p.2) < C} ∩
       {p : ℝ≥0 × Ω | Y p.1 p.2 ∈ Icc a b})
    exact hInterior.inter hBand
  have hEstrip : ∀ p ∈ E,
      Y p.1 p.2 ∈ Icc a b := by
    intro p hp
    exact hp.2
  simpa only [E, Y] using
    (avram_wave7_17_original_compact_actual_negative_jump_expected_nonpos
      X hBV T C hC w hw_cont hw0 hw_neg hw_smooth hw_grad q x hq
      D hD a b L R ha ha2 hab hL hR hLip hWbound hCapBand
      E hEm hEstrip hMass)
