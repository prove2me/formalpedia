-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_BV_physical_compact_C1_intrinsic_NT_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:12:12.529145+00:00
-- url     : https://prove2.me/submissions/973196c5-bde9-44d2-90d3-e63f1b8d28bd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_intrinsic_weighted_negative_mark_mass_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_discounted_compact_C1_negative_mark_absolute_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_admissible_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_negative_mark_value_kernel_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual discounted compact C1 physical jump kernel is integrable
    against the intrinsic BV Lévy jump count on the same finite clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q a b L R : ℝ) (hq : 0 ≤ q) (ha : 0 < a)
    (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0),
      let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      let E : Set (ℝ≥0 × ℝ) :=
        {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
      let K : ℝ≥0 × ℝ → ℝ := fun p =>
        if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
      let G : ℝ≥0 × ℝ → ℝ := fun p =>
        Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
      let Δ : ℝ≥0 → ℝ := fun v =>
        X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
      let NT : Measure (ℝ≥0 × ℝ) :=
        ((Measure.count.restrict
          ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ Ioc 0 T)).map
            (fun v : ℝ≥0 => (v, Δ v)))
      Integrable G NT := by
  filter_upwards
    [AvramDividend.Classical.avram_bv_cell7_original_BV_intrinsic_weighted_negative_mark_mass_finite
      X hBV] with ω hω
  intro T
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let E : Set (ℝ≥0 × ℝ) :=
    {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
  let K : ℝ≥0 × ℝ → ℝ := fun p =>
    if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
  let G : ℝ≥0 × ℝ → ℝ := fun p =>
    Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
  let Δ : ℝ≥0 → ℝ := fun v =>
    X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
  let NT : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict
      ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ Ioc 0 T)).map
        (fun v : ℝ≥0 => (v, Δ v)))
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
  have hG : Measurable G :=
    hExp.mul (Measurable.ite hE hK measurable_const)
  have hCoeff : 0 ≤ L + 4 * R / a :=
    add_nonneg hL (div_nonneg (by nlinarith [hR]) (le_of_lt ha))
  have hτT : τ ≤ T := by
    have hrfinite : min (ruinTime X x D ω) (T : ℝ≥0∞) < ⊤ :=
      lt_of_le_of_lt (min_le_right _ _) ENNReal.coe_lt_top
    have hco : (τ : ℝ≥0∞) =
        min (ruinTime X x D ω) (T : ℝ≥0∞) :=
      ENNReal.coe_toNNReal (ne_of_lt hrfinite)
    have hle : (τ : ℝ≥0∞) ≤ (T : ℝ≥0∞) := by
      rw [hco]
      exact min_le_right _ _
    exact_mod_cast hle
  have hdom : ∀ p : ℝ≥0 × ℝ,
      |G p| ≤ (L + 4 * R / a) * max (-p.2) 0 := by
    intro p
    by_cases hp : p ∈ E
    · have hT : p.1 ≤ T := hp.1.trans hτT
      have hy : Y p.1 ∈ Icc a b := hp.2.1
      have hz : p.2 < 0 := hp.2.2
      simp only [G, if_pos hp, K, if_pos hT,
        max_eq_left (le_of_lt (neg_pos.mpr hz))]
      exact AvramDividend.Classical.avram_bv_cell7_original_discounted_compact_C1_negative_mark_absolute_envelope
        w a b L R ha hab hL hR hLip hWbound q hq p.1 (Y p.1) p.2 hy hz
    · simp only [G, if_neg hp, mul_zero, abs_zero]
      exact mul_nonneg hCoeff (le_max_right _ _)
  have hfinite : (∫⁻ p, ENNReal.ofReal
      ((L + 4 * R / a) * (-p.2)) ∂NT) < ⊤ :=
    hω T (L + 4 * R / a) hCoeff
  have hpoint : ∀ p : ℝ≥0 × ℝ,
      ‖G p‖ₑ ≤ ENNReal.ofReal ((L + 4 * R / a) * (-p.2)) := by
    intro p
    rw [Real.enorm_eq_ofReal_abs]
    have hupper : ENNReal.ofReal |G p| ≤
        ENNReal.ofReal ((L + 4 * R / a) * max (-p.2) 0) :=
      ENNReal.ofReal_le_ofReal (hdom p)
    have hclip : ENNReal.ofReal ((L + 4 * R / a) * max (-p.2) 0) =
        ENNReal.ofReal ((L + 4 * R / a) * (-p.2)) := by
      by_cases hp : 0 ≤ -p.2
      · simp [max_eq_left hp]
      · have hle : -p.2 ≤ 0 := le_of_lt (lt_of_not_ge hp)
        have hprod : (L + 4 * R / a) * (-p.2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hCoeff hle
        calc
          ENNReal.ofReal ((L + 4 * R / a) * max (-p.2) 0) = 0 := by
            rw [max_eq_right hle, mul_zero]
            exact ENNReal.ofReal_zero
          _ = ENNReal.ofReal ((L + 4 * R / a) * (-p.2)) :=
            (ENNReal.ofReal_of_nonpos hprod).symm
    exact hupper.trans_eq hclip
  change Integrable G NT
  refine ⟨hG.aestronglyMeasurable, ?_⟩
  change (∫⁻ p, ‖G p‖ₑ ∂NT) < ⊤
  exact lt_of_le_of_lt (lintegral_mono hpoint) hfinite
