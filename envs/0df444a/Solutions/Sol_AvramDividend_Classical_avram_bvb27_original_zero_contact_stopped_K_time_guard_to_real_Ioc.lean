-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb27_original_zero_contact_stopped_K_time_guard_to_real_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:17:54.827092+00:00
-- url     : https://prove2.me/submissions/6516f092-2099-4b6b-8f0b-065dbc84228b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb27_original_clipped_prefix_survival_ruin_guard_redundant
import Theorems.Thm_AvramDividend_Classical_avram_bvb27_original_mapped_finite_clock_discounted_prefix_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
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
      (∫ t : ℝ≥0,
        (if 0 < t ∧ (t : ℝ) < T - δ n ∧
             (t : ℝ≥0∞) ≤ ruinTime X x D ω then
           -(Real.exp (-(q * (t : ℝ))) * w 0) *
             (X.ν (Iio (0 : ℝ))).toReal
         else 0)
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) =
        -(w 0 * (X.ν (Iio (0 : ℝ))).toReal) *
          (∫ t in Ioc (0 : ℝ) (T - δ n),
            Real.exp (-(q * t)) ∂(volume : Measure ℝ))  := by
  classical
  intro δ U H K n
  let b : ℝ := T - T / ((n : ℝ) + 2)
  let mass : ℝ := (X.ν (Iio (0 : ℝ))).toReal
  let c : ℝ := -(w 0 * mass)
  have hDelta : 0 ≤ T / ((n : ℝ) + 2) := by positivity
  have hbT : b ≤ T := sub_le_self T hDelta
  have hb0 : 0 ≤ b := by
    have hDen : 1 ≤ (n : ℝ) + 2 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact sub_nonneg.mpr (div_le_self hT.le hDen)
  have hPoint (t : ℝ≥0) :
      (if 0 < t ∧ (t : ℝ) < b ∧
          (t : ℝ≥0∞) ≤ ruinTime X x D ω then
        -(Real.exp (-(q * (t : ℝ))) * w 0) * mass
       else 0) =
      c * (if 0 < t ∧ (t : ℝ) < b then
        Real.exp (-(q * (t : ℝ))) else 0) := by
    by_cases ht : 0 < t ∧ (t : ℝ) < b
    · have hRuin : (t : ℝ≥0∞) ≤ ruinTime X x D ω := by
        exact avram_bvb27_original_clipped_prefix_survival_ruin_guard_redundant
          X x D ω T hT S hS hSurvival n t ht.2
      simp only [ht.1, ht.2, hRuin, and_self, and_true, if_pos]
      dsimp only [c, mass]
      ring
    · have hFail : ¬ (0 < t ∧ (t : ℝ) < b ∧
          (t : ℝ≥0∞) ≤ ruinTime X x D ω) := by
        exact fun h => ht ⟨h.1,h.2.1⟩
      simp [ht,hFail]
  have hClock :=
    avram_bvb27_original_mapped_finite_clock_discounted_prefix_integral
      q T b hT hb0 hbT
  calc
    (∫ t : ℝ≥0,
      (if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
          (t : ℝ≥0∞) ≤ ruinTime X x D ω then
        -(Real.exp (-(q * (t : ℝ))) * w 0) * mass
       else 0)
       ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) =
      c * (∫ t : ℝ≥0,
        (if 0 < t ∧ (t : ℝ) < b then
          Real.exp (-(q * (t : ℝ))) else 0)
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) := by
          calc
            _ = (∫ t : ℝ≥0, c * (if 0 < t ∧ (t : ℝ) < b then
                Real.exp (-(q * (t : ℝ))) else 0)
                ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) := by
                  apply integral_congr_ae
                  exact Filter.Eventually.of_forall (fun t => hPoint t)
            _ = _ := by rw [integral_const_mul]
    _ = c * (∫ t in Ioc (0 : ℝ) b,
         Real.exp (-(q * t)) ∂(volume : Measure ℝ)) := by rw [hClock]
    _ = -(w 0 * (X.ν (Iio (0 : ℝ))).toReal) *
        (∫ t in Ioc (0 : ℝ) (T - T / ((n : ℝ) + 2)),
          Real.exp (-(q * t)) ∂(volume : Measure ℝ)) := rfl
