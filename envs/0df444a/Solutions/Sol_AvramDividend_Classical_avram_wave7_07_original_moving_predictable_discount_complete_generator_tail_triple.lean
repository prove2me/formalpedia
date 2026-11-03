-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_moving_predictable_discount_complete_generator_tail_triple
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:58:56.619691+00:00
-- url     : https://prove2.me/submissions/810d541b-bb5c-45c9-99ef-32c648bb178a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_moving_predictable_discount_adaptive_L1_tail_vanishes
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_moving_predictable_discount_adaptive_L2_tail_vanishes
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_moving_predictable_discount_signed_generator_tail_vanishes

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Bundle source-faithful, jointly predictable nonlinear jump Taylor L1, L2,
and signed-generator drift cutoff convergence for moving discounts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (S : ℕ → Set ((ℝ≥0 × Ω) × ℝ))
    (hSm : ∀ n, MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] (S n))
    (hSanti : Antitone S) (hSempty : (⋂ n, S n) = ∅)
    (a : ℕ → ℝ≥0 × Ω → ℝ)
    (ham : ∀ n, Measurable[𝓕.rightCont.predictable] (a n))
    (ha : ∀ n p, 0 ≤ a n p ∧ a n p ≤ 1) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    (Tendsto (fun n : ℕ =>
      ∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        (S n).indicator (fun r => ENNReal.ofReal (|a n r.1 * HS r|)) p
          ∂(letI : MeasurableSpace (ℝ≥0 × Ω) :=
             𝓕.rightCont.predictable
            μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
      atTop (𝓝 0)) ∧
    (Tendsto (fun n : ℕ =>
      ∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        (S n).indicator (fun r => ENNReal.ofReal ((a n r.1 * HS r) ^ 2)) p
          ∂(letI : MeasurableSpace (ℝ≥0 × Ω) :=
             𝓕.rightCont.predictable
            μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
      atTop (𝓝 0)) ∧
    (Tendsto (fun n : ℕ =>
      ∫ p : ((ℝ≥0 × Ω) × ℝ),
        (S n).indicator (fun r => a n r.1 * HS r) p
          ∂(letI : MeasurableSpace (ℝ≥0 × Ω) :=
             𝓕.rightCont.predictable
            μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
      atTop (𝓝 0)) := by
  classical
  intro Y H HS
  constructor
  · exact avram_wave7_07_original_moving_predictable_discount_adaptive_L1_tail_vanishes
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ S hSm hSanti hSempty a ham ha
  constructor
  · exact avram_wave7_07_original_moving_predictable_discount_adaptive_L2_tail_vanishes
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ S hSm hSanti hSempty a ham ha
  · exact avram_wave7_07_original_moving_predictable_discount_signed_generator_tail_vanishes
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ S hSm hSanti hSempty a ham ha
