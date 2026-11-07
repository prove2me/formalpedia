-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_discounted_C1_signed_global_NX_real_eq_stopped_jump_series
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:52:08.836859+00:00
-- url     : https://prove2.me/submissions/10c111f2-87f9-49c6-b628-fe692e500137

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_admissible_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_negative_mark_value_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_global_NX_integrable_signed_real_eq_stopped_jump_series

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The genuine original discounted nonlinear C1 kernel, if integrable on
    original global NX, is the difference of its actual stopped jump series. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q c a b : ℝ) (T : ℝ≥0) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
        (fun v : ℝ≥0 => (v, Δ v)))
    let E : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    let G : ℝ≥0 × ℝ → ℝ := fun p =>
      c * Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
    Integrable G NX →
      (∫ p, G p ∂NX) =
        (∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc 0 (min T τ) then
            ENNReal.ofReal (G (v, Δ v)) else 0).toReal -
        (∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc 0 (min T τ) then
            ENNReal.ofReal (-G (v, Δ v)) else 0).toReal := by
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let Δ : ℝ≥0 → ℝ := fun v =>
    X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
      (fun v : ℝ≥0 => (v, Δ v)))
  let E : Set (ℝ≥0 × ℝ) :=
    {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
  let K : ℝ≥0 × ℝ → ℝ := fun p =>
    if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
  let G : ℝ≥0 × ℝ → ℝ := fun p =>
    c * Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
  have hYpair : Measurable (fun t : ℝ≥0 => (t, ω)) :=
    measurable_id.prodMk measurable_const
  have hY : Measurable Y :=
    (AvramDividend.Classical.avram_p3_e_compensator_original_admissible_prestate_ambient_measurable
      X x C D hD).comp hYpair
  have hE : MeasurableSet E := by
    have ht : MeasurableSet {p : ℝ≥0 × ℝ | p.1 ≤ τ} := by
      change MeasurableSet ((fun p : ℝ≥0 × ℝ => p.1) ⁻¹' Iic τ)
      exact measurable_fst measurableSet_Iic
    have hb : MeasurableSet {p : ℝ≥0 × ℝ | Y p.1 ∈ Icc a b} := by
      change MeasurableSet ((fun p : ℝ≥0 × ℝ => Y p.1) ⁻¹' Icc a b)
      exact (hY.comp measurable_fst) measurableSet_Icc
    have hz : MeasurableSet {p : ℝ≥0 × ℝ | p.2 < 0} := by
      change MeasurableSet ((fun p : ℝ≥0 × ℝ => p.2) ⁻¹' Iio 0)
      exact measurable_snd measurableSet_Iio
    exact ht.inter (hb.inter hz)
  have hMap : Measurable (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) :=
    (measurable_fst.prodMk measurable_const).prodMk measurable_snd
  have hK : Measurable K :=
    (AvramDividend.Classical.avram_wave7_17_original_finite_clock_negative_mark_value_kernel_measurable
      X x D hD.1.1 w hw_cont hw_neg T).comp hMap
  have hExp : Measurable (fun p : ℝ≥0 × ℝ =>
      Real.exp (-(q * (p.1 : ℝ)))) := by fun_prop
  have hMasked : Measurable (fun p : ℝ≥0 × ℝ =>
      if p ∈ E then K p else 0) := Measurable.ite hE hK measurable_const
  have hG : Measurable G := (measurable_const.mul hExp).mul hMasked
  have hSupport : ∀ p : ℝ≥0 × ℝ, min T τ < p.1 → G p = 0 := by
    intro p hp
    by_cases hT : p.1 ≤ T
    · have hnτ : ¬p.1 ≤ τ := by
        intro hτ
        exact (not_lt_of_ge (le_min hT hτ)) hp
      have hnE : p ∉ E := fun he => hnτ he.1
      simp [G, hnE]
    · simp [G, K, hT]
  change Integrable G NX → _
  intro hInt
  simpa only [NX, Δ] using
    (AvramDividend.Classical.avram_bv_cell7_original_global_NX_integrable_signed_real_eq_stopped_jump_series
      X ω (min T τ) G hG hSupport hInt)
