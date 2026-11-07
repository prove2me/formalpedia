-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_discounted_C1_nonlinear_global_NX_stopped_cell_source_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:35:27.390406+00:00
-- url     : https://prove2.me/submissions/8da297d0-a497-47fd-b4d7-fd398fba2393

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_admissible_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_negative_mark_value_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_global_NX_stopped_physical_grid_marked_source_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The actual discounted compact-band C1 jump source in the global
    compensated Lévy measure is exactly the same original stopped grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q c a b : ℝ) (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
        (fun v : ℝ≥0 => (v, Δ v)))
    let N : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
      (Measure.count.restrict ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ I)).map
        (fun v : ℝ≥0 => (v, Δ v))
    let E : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    let F : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
      ENNReal.ofReal (c * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ E then K p else 0))
    u 0 = 0 ∧ u (m + 1) = min T τ ∧
      (∫⁻ p, (if p.1 ∈ Ioc (u 0) (u (m + 1)) then F p else 0) ∂NX) =
        (∫⁻ p, F p ∂N (Ioc (u 0) (u (m + 1)))) ∧
      (∫⁻ p, (if p.1 ∈ Ioc (u 0) (u (m + 1)) then F p else 0) ∂NX) =
        ∑ i ∈ Finset.range (m + 1),
          (∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
              F (v, Δ v) else 0) := by
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun i =>
    min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
  let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let Δ : ℝ≥0 → ℝ := fun v =>
    X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
      (fun v : ℝ≥0 => (v, Δ v)))
  let N : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
    (Measure.count.restrict ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ I)).map
      (fun v : ℝ≥0 => (v, Δ v))
  let E : Set (ℝ≥0 × ℝ) :=
    {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
  let K : ℝ≥0 × ℝ → ℝ := fun p =>
    if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
  let F : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (c * Real.exp (-(q * (p.1 : ℝ))) *
      (if p ∈ E then K p else 0))
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
  have hF : Measurable F :=
    ENNReal.measurable_ofReal.comp ((measurable_const.mul hExp).mul hMasked)
  exact AvramDividend.Classical.avram_bv_cell7_original_global_NX_stopped_physical_grid_marked_source_identity
    X x D T m ω F hF
