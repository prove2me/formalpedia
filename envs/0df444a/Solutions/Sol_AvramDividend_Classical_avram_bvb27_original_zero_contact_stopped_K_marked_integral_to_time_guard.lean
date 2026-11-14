-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb27_original_zero_contact_stopped_K_marked_integral_to_time_guard
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:24:35.871716+00:00
-- url     : https://prove2.me/submissions/d0c6d02e-817d-4ada-87d5-b81ebb47b37e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb25_original_zero_contact_stopped_K_global_mark_guard_exact
import Theorems.Thm_AvramDividend_Classical_avram_bvb25_original_restricted_negative_mark_guard_integral_const
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_neg : ∀ z < 0, w z = 0)
    (q T : ℝ) (hT : 0 < T) (ω : Ω)
    (S : ℝ≥0) (hS : (S : ℝ) = T)
    (hSource : ∀ t : ℝ≥0, t ≤ S →
       X.X t ω = (t : ℝ) * X.drift)
    (hZero : ∀ t : ℝ≥0, t ≤ S →
       riskProcess X x D t ω = 0)
    (hSurvival : (S : ℝ≥0∞) < ruinTime X x D ω) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → ℝ≥0 → ℝ → ℝ := fun n t z =>
      if 0 < t ∧ (t : ℝ) < T - δ n ∧
          (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
          0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C ∧ z < 0 then
        Real.exp (-(q * (t : ℝ))) *
          (w (U t + z) - w (U t)) else 0
    let K : ℕ → ℝ := fun n =>
      ∫ t, ∫ z, H n t z ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    ∀ n : ℕ,
      K n = ∫ t : ℝ≥0,
        (if 0 < t ∧ (t : ℝ) < T - δ n ∧
             (t : ℝ≥0∞) ≤ ruinTime X x D ω then
           -(Real.exp (-(q * (t : ℝ))) * w 0) *
             (X.ν (Iio (0 : ℝ))).toReal
         else 0)
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal) := by
  classical
  intro δ U H K n
  let Q : ℝ≥0 → Prop := fun t =>
    0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
      (t : ℝ≥0∞) ≤ ruinTime X x D ω
  let a : ℝ≥0 → ℝ := fun t =>
    -(Real.exp (-(q * (t : ℝ))) * w 0)
  have hIntegrand (t : ℝ≥0) (z : ℝ) :
      (if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
          (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
          0 ≤ Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
          ENNReal.ofReal (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ C ∧ z < 0 then
        Real.exp (-(q * (t : ℝ))) *
          (w (Function.leftLim
             (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t + z) -
           w (Function.leftLim
             (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))
       else 0) = (if Q t ∧ z < 0 then a t else 0) := by
    simpa only [Q, a, and_assoc] using
      (avram_bvb25_original_zero_contact_stopped_K_global_mark_guard_exact
         X x C D hD ω T hT S hS hSource hZero w hw_neg q n t z)
  have hMark (t : ℝ≥0) :
     (∫ z : ℝ, (if Q t ∧ z < 0 then a t else 0)
       ∂(X.ν.restrict (Iio (0 : ℝ)))) =
       if Q t then a t * (X.ν (Iio (0 : ℝ))).toReal else 0 := by
    by_cases ht : Q t
    · simp only [ht, true_and]
      exact avram_bvb25_original_restricted_negative_mark_guard_integral_const
        X (a t)
    · simp [ht]
  change
      (∫ t : ℝ≥0, ∫ z : ℝ,
        (if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
            (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
            0 ≤ Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
            ENNReal.ofReal (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ C ∧
            z < 0 then
          Real.exp (-(q * (t : ℝ))) *
            (w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t + z) -
              w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))
         else 0) ∂(X.ν.restrict (Iio (0 : ℝ)))
         ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) = _
  simp_rw [hIntegrand]
  simp_rw [hMark]
  rfl
