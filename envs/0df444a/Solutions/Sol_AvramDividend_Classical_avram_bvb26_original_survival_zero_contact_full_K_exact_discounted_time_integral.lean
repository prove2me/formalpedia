-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb26_original_survival_zero_contact_full_K_exact_discounted_time_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:12:07.168847+00:00
-- url     : https://prove2.me/submissions/7ea348a8-4cf2-438e-bbea-c9d60068c1ab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb27_original_zero_contact_stopped_K_marked_integral_to_time_guard
import Theorems.Thm_AvramDividend_Classical_avram_bvb27_original_zero_contact_stopped_K_time_guard_to_real_Ioc
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
      K n = -(w 0 * (X.ν (Iio (0 : ℝ))).toReal) *
        (∫ t in Ioc (0 : ℝ) (T - δ n),
          Real.exp (-(q * t)) ∂(volume : Measure ℝ)) := by
  intro δ U H K n
  have hMarks :=
    avram_bvb27_original_zero_contact_stopped_K_marked_integral_to_time_guard
      X x C D hD w hw_neg q T hT ω S hS hSource hZero hSurvival n
  have hTime :=
    avram_bvb27_original_zero_contact_stopped_K_time_guard_to_real_Ioc
      X x C D hD w hw_neg q T hT ω S hS hSource hZero hSurvival n
  exact hMarks.trans hTime
