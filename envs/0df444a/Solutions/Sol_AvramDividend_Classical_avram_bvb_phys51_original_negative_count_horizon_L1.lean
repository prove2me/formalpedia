-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys51_original_negative_count_horizon_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T15:44:38.099046+00:00
-- url     : https://prove2.me/submissions/e82fe904-2cc1-446f-b5db-79e30ce50217

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let J : ℕ → Ω → ℝ := fun n ω =>
      ∫ p, H n ((p.1, ω), p.2) ∂(NX ω)
    let N : Ω → ℝ := fun ω =>
      ((NX ω) (Ioc (0 : ℝ≥0) (Real.toNNReal T) ×ˢ Iio (0 : ℝ))).toReal
    Integrable N P := by
  let N : Ω → ℝ := fun ω =>
    (((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t, X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
      (Ioc (0 : ℝ≥0) (Real.toNNReal T) ×ˢ Iio (0 : ℝ))).toReal
  change Integrable N P
  letI : IsProbabilityMeasure P := X.isProbability
  have hFiniteν : X.ν (Iio (0 : ℝ)) ≠ ⊤ := ne_top_of_lt hActivity
  have hSq : Integrable (fun ω => N ω ^ 2) P := by
    simpa only [N] using
      (avram_anoise18_original_total_negative_count_finite_activity_L2
        X hFiniteν (Real.toNNReal T)).1
  have hMeas : Measurable N := by
    simpa only [N] using
      (avram_p2_e_compensator_intrinsic_rectangle_count_measurable
        X 0 (Real.toNNReal T) (by positivity) (Iio (0 : ℝ))
        measurableSet_Iio).ennreal_toReal
  have hDom : Integrable (fun ω => N ω ^ 2 + 1) P :=
    hSq.add (integrable_const 1)
  have hBound : ∀ ω, ‖N ω‖ ≤ N ω ^ 2 + (1 : ℝ) := by
    intro ω
    rw [Real.norm_eq_abs]
    have hNonneg : 0 ≤ N ω := ENNReal.toReal_nonneg
    rw [abs_of_nonneg hNonneg]
    nlinarith [sq_nonneg (N ω - 1)]
  exact hDom.mono' hMeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hBound)
