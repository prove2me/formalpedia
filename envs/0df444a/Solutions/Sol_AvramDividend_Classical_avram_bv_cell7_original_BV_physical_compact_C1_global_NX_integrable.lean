-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_BV_physical_compact_C1_global_NX_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:26:17.138571+00:00
-- url     : https://prove2.me/submissions/9f97ae14-38a4-4505-9c64-56a14057c217

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_physical_compact_C1_intrinsic_NT_integrable
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_global_NX_finite_clock_intrinsic_NT_absolute_source_identity
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_admissible_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_negative_mark_value_kernel_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual stopped physical C1 kernel is integrable on the original
    global NX, transferred from the finite same-path intrinsic jump measure. -/
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
      let NX : Measure (ℝ≥0 × ℝ) :=
        ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
          (fun v : ℝ≥0 => (v, Δ v)))
      Integrable G NX := by
  filter_upwards
    [AvramDividend.Classical.avram_bv_cell7_original_BV_physical_compact_C1_intrinsic_NT_integrable
      X hBV x C D hD w hw_cont hw_neg q a b L R hq ha hab hL hR hLip hWbound]
    with ω hω
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
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
      (fun v : ℝ≥0 => (v, Δ v)))
  let NT : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict
      ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ Ioc 0 T)).map
        (fun v : ℝ≥0 => (v, Δ v)))
  have hIntNT : Integrable G NT := hω T
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
  have hSupport : ∀ p : ℝ≥0 × ℝ, T < p.1 → G p = 0 := by
    intro p hp
    have hnotE : p ∉ E := by
      intro he
      exact (not_lt_of_ge (he.1.trans hτT)) hp
    simp [G, hnotE]
  have hTransfer : (∫⁻ p, ENNReal.ofReal |G p| ∂NX) =
      (∫⁻ p, ENNReal.ofReal |G p| ∂NT) :=
    AvramDividend.Classical.avram_bv_cell7_original_global_NX_finite_clock_intrinsic_NT_absolute_source_identity
      X ω T G hG hSupport
  have hfinite : (∫⁻ p, ENNReal.ofReal |G p| ∂NT) < ⊤ := by
    have hNormFinite : (∫⁻ p, ‖G p‖ₑ ∂NT) < ⊤ :=
      hIntNT.hasFiniteIntegral
    simpa only [Real.enorm_eq_ofReal_abs] using hNormFinite
  have hfiniteNX : (∫⁻ p, ENNReal.ofReal |G p| ∂NX) < ⊤ := by
    rw [hTransfer]
    exact hfinite
  refine ⟨hG.aestronglyMeasurable, ?_⟩
  change (∫⁻ p, ‖G p‖ₑ ∂NX) < ⊤
  simpa only [Real.enorm_eq_ofReal_abs] using hfiniteNX
