-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_moving_signed_predictable_unit_generator_tail_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:10:09.958576+00:00
-- url     : https://prove2.me/submissions/0b1b88a0-87f6-476e-9e7c-a78cf4431e3b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_moving_signed_predictable_unit_contraction_L1_tail_vanishes
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Signed original Lévy nonlinear generator drift tails vanish for moving
predictable unit contractions of either sign and adaptive marked cutoffs. -/
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
    (ha : ∀ n p, |a n p| ≤ 1) :
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
    Tendsto (fun n : ℕ =>
      ∫ p : ((ℝ≥0 × Ω) × ℝ),
        (S n).indicator (fun r => a n r.1 * HS r) p
          ∂(letI : MeasurableSpace (ℝ≥0 × Ω) :=
             𝓕.rightCont.predictable
            μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
      atTop (𝓝 0) := by
  classical
  intro Y H HS
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)
  letI : SFinite (X.ν.restrict (Iio (0 : ℝ))) :=
    levy_negative_jump_measure_sFinite X
  let M := μ.prod (X.ν.restrict (Iio (0 : ℝ)))
  let f : ℕ → ((ℝ≥0 × Ω) × ℝ) → ℝ := fun n p => a n p.1 * HS p
  let E : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
      (S n).indicator (fun r => ENNReal.ofReal (|f n r|)) p ∂M
  have hTail :
      Tendsto E atTop (𝓝 0) :=
    avram_wave7_07_original_moving_signed_predictable_unit_contraction_L1_tail_vanishes
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ S hSm hSanti hSempty a ham ha
  have hRealTail : Tendsto (fun n => (E n).toReal) atTop (𝓝 0) := by
    have hCont : Tendsto ENNReal.toReal (𝓝 (0 : ℝ≥0∞)) (𝓝 (0 : ℝ)) := by
      simpa using (ENNReal.tendsto_toReal (a := 0) (by simp))
    have hComp := hCont.comp hTail
    change Tendsto (fun n => (E n).toReal) atTop (𝓝 (0 : ℝ)) at hComp
    exact hComp
  have hPoint (n : ℕ) (p : ((ℝ≥0 × Ω) × ℝ)) :
      ENNReal.ofReal (‖(S n).indicator (f n) p‖) =
        (S n).indicator (fun r => ENNReal.ofReal (|f n r|)) p := by
    by_cases hp : p ∈ S n
    · simp only [Set.indicator_of_mem hp, Real.norm_eq_abs]
    · simp only [Set.indicator_of_notMem hp]
      simp
  have hBound (n : ℕ) :
      ‖∫ p, (S n).indicator (f n) p ∂M‖ ≤ (E n).toReal := by
    have hNorm := norm_integral_le_lintegral_norm ((S n).indicator (f n)) (μ := M)
    calc
      ‖∫ p, (S n).indicator (f n) p ∂M‖ ≤
          (∫⁻ p, ENNReal.ofReal (‖(S n).indicator (f n) p‖) ∂M).toReal := hNorm
      _ = (E n).toReal := by
        congr 1
        exact lintegral_congr (fun p => hPoint n p)
  have hNormTend :
      Tendsto (fun n => ‖∫ p, (S n).indicator (f n) p ∂M‖)
        atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) hBound hRealTail
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hNormTend
