-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_original_uniform_same_source_HJB_and_positive_cash_budget_failure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:17:20.273692+00:00
-- url     : https://prove2.me/submissions/252d27ac-730d-460a-b5ea-b96f4d65aed5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_BV_positive_nojump_path_witness
import Theorems.Thm_AvramDividend_Classical_avram_b29_original_positive_probability_drift_source_failure
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_unit_drift_forces_c_half
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_positivecap_affine_candidate_HJB_bundle
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_barrier_admissible_at_any_positive_cap
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_half_affine_preruin_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_zero_barrier_HJB_right_payment_automatic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
theorem solution :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.BoundedVariation ∧
      X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0) ∧
      X.ν (Iio (0 : ℝ)) < ⊤ ∧ X.drift = 1 ∧ X.σ = 0 ∧
      0 < P {ω |
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ (X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (1 : ℝ≥0) ×ˢ Iio (0 : ℝ)) = 0 ∧
        (∀ t : ℝ≥0, t ≤ 1 → X.X t ω = (t : ℝ) * X.drift)} ∧ 0 < P {ω |
        let D := barrierStrategy X 0 0
        let T : ℝ := 1 / 10
        let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
        let u : ℕ → ℕ → ℝ≥0 := fun n i =>
          ⟨(1 / 10 : ℝ) * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
        let F : ℕ → ℝ := fun n =>
          (∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩
              Iio (T - T / ((n : ℝ) + 2)),
            ENNReal.ofReal (Real.exp (-t)) ∂(dividendMeasure D ω)).toReal +
            (if ((1 / 10 : ℝ≥0) : ℝ≥0∞) < ruinTime X 0 D ω then
              Real.exp (-T) * w (riskProcess X 0 D (1 / 10 : ℝ≥0) ω) else 0)
        let L : ℕ → ℝ := fun n =>
          let Z : ℕ → ℝ := fun i => Function.leftLim
            (fun t : ℝ≥0 => (0 : ℝ) + X.X t ω - rightLimit D t ω) (u n i)
          ∑ i ∈ Finset.range (n + 1),
            if (u n i : ℝ≥0∞) < ruinTime X 0 D ω ∧
                0 < Z i ∧ ENNReal.ofReal (Z i) < (1 : ℝ≥0∞) then
              Real.exp (-(u n i : ℝ)) *
                (X.drift * deriv w (Z i) - w (Z i)) * ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0
        ¬ Tendsto (fun n => max (F n - (w 0 + L n)) 0)
          atTop (𝓝 (0 : ℝ))} ∧ (let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
       let D := barrierStrategy X 0 0
       let C : ℝ≥0∞ := 1
       ContinuousOn w (Ici 0) ∧ 0 ≤ w 0 ∧
         (∀ z : ℝ, z < 0 → w z = 0) ∧
         ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
         (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
           X.GeneratorIntegrable w y ∧ X.generator w y - w y ≤ 0) ∧
         (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) ∧ IsAdmissibleLe X 0 C D ∧
         (∀ ω (t : ℝ≥0), 0 < t →
           (t : ℝ≥0∞) < ruinTime X 0 D ω → 0 ≤ w (riskProcess X 0 D t ω)) ∧
         (∀ ω (t : ℝ≥0),
           (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X 0 D ω) → rightLimit D t ω - D t ω ≤
             w (riskProcess X 0 D t ω) -
               w (riskProcess X 0 D t ω - (rightLimit D t ω - D t ω)))) := by
  obtain ⟨P, 𝓕, X, hs, hbv, hν, hfinite, hd, hσ, hPos⟩ :=
    avram_bvb_obstruction_original_uniform_BV_positive_nojump_path_witness
      (1 : ℝ≥0)
  have hc : X.c = 1 / 2 :=
    avram_bvb_obstruction_original_uniform_unit_drift_forces_c_half X hν hd
  have hAnal :=
    avram_bvb_obstruction_original_uniform_positivecap_affine_candidate_HJB_bundle
      X hν hσ hc (1 : ℝ≥0∞)
  dsimp at hAnal
  rcases hAnal with ⟨hcOnt, h0, hneg, hsmooth, hGen, hGrad⟩
  let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
  let D := barrierStrategy X 0 0
  have hAdm : IsAdmissibleLe X 0 (1 : ℝ≥0∞) D :=
    avram_bvb22_original_zero_barrier_admissible_at_any_positive_cap
      X 1 (by norm_num)
  have hNonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X 0 D ω →
      0 ≤ w (riskProcess X 0 D t ω) := by
    exact avram_bvb_obstruction_original_half_affine_preruin_nonnegative
      X 0 D
  have hJump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X 0 D ω) →
      rightLimit D t ω - D t ω ≤
      w (riskProcess X 0 D t ω) -
        w (riskProcess X 0 D t ω -
          (rightLimit D t ω - D t ω)) :=
    avram_bvb_obstruction_original_zero_barrier_HJB_right_payment_automatic
      X w
  let E : Set ((ℕ → ℝ) × (ℕ → ℝ)) := {ω |
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ (X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (1 : ℝ≥0) ×ˢ Iio (0 : ℝ)) = 0 ∧
    (∀ t : ℝ≥0, t ≤ 1 → X.X t ω = (t : ℝ) * X.drift)}
  have hPath : ∀ ω ∈ E, ∀ t : ℝ≥0, t ≤ (1 : ℝ≥0) →
      X.X t ω = (t : ℝ) * X.drift := by
    intro ω hω t ht
    exact hω.2 t ht
  have hBad := avram_b29_original_positive_probability_drift_source_failure
    X E hPos hd hPath
  refine ⟨P, 𝓕, X, hs, hbv, hν, hfinite, hd, hσ, hPos, hBad, ?_⟩
  dsimp
  exact ⟨hcOnt, h0, hneg, hsmooth, hGen, hGrad, hAdm, hNonneg, hJump⟩
