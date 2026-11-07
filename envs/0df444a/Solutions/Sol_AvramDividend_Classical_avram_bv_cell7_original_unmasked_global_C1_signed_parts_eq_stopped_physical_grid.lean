-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_unmasked_global_C1_signed_parts_eq_stopped_physical_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:51:54.875903+00:00
-- url     : https://prove2.me/submissions/f1d8acd2-c359-4a1b-b140-868a0c75ce53

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_admissible_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_negative_mark_value_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_discounted_C1_nonlinear_global_NX_stopped_cell_source_identity
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_discounted_C1_nonlinear_source_exact_stopped_clock_support
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_global_NX_upper_clock_supported_source_unmasked

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The global original compensated-measure C1 jump source, with no extra
    cutoff, is the exact same original stopped physical-cell source. -/
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
      (∫⁻ p, F p ∂NX) =
        (∫⁻ p, F p ∂N (Ioc (u 0) (u (m + 1)))) ∧
      (∫⁻ p, F p ∂NX) =
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
  obtain ⟨h0, hEnd, hLink, hGrid⟩ :=
    (AvramDividend.Classical.avram_bv_cell7_original_discounted_C1_nonlinear_global_NX_stopped_cell_source_identity
      X x C D hD w hw_cont hw_neg q c a b T m ω)
  have hStop : ∀ p : ℝ≥0 × ℝ, min T τ < p.1 → F p = 0 := by
    simpa only [τ, Y, E, K, F] using
      (AvramDividend.Classical.avram_bv_cell7_original_discounted_C1_nonlinear_source_exact_stopped_clock_support
        X x D w q c a b T ω)
  have hUnmask :
      (∫⁻ p, F p ∂NX) =
      (∫⁻ p, (if p.1 ∈ Ioc 0 (min T τ) then F p else 0) ∂NX) := by
    simpa only [NX, Δ] using
      (AvramDividend.Classical.avram_bv_cell7_original_global_NX_upper_clock_supported_source_unmasked
        X ω (min T τ) F hF hStop)
  have hCut :
      (∫⁻ p, (if p.1 ∈ Ioc 0 (min T τ) then F p else 0) ∂NX) =
      (∫⁻ p, (if p.1 ∈ Ioc (u 0) (u (m + 1)) then F p else 0) ∂NX) := by
    have heq : Ioc 0 (min T τ) = Ioc (u 0) (u (m + 1)) :=
      congrArg₂ Ioc h0.symm hEnd.symm
    have hfun :
        (fun p : ℝ≥0 × ℝ =>
          if p.1 ∈ Ioc 0 (min T τ) then F p else 0) =
        (fun p : ℝ≥0 × ℝ =>
          if p.1 ∈ Ioc (u 0) (u (m + 1)) then F p else 0) := by
      funext p
      have hmem : (p.1 ∈ Ioc 0 (min T τ)) ↔
          (p.1 ∈ Ioc (u 0) (u (m + 1))) := by
        rw [heq]
      by_cases hp : p.1 ∈ Ioc 0 (min T τ)
      · simp only [if_pos hp, if_pos (hmem.mp hp)]
      · have hn : p.1 ∉ Ioc (u 0) (u (m + 1)) :=
          fun h => hp (hmem.mpr h)
        simp only [if_neg hp, if_neg hn]
    exact congrArg (fun f : (ℝ≥0 × ℝ) → ℝ≥0∞ => ∫⁻ p, f p ∂NX) hfun
  have hFull := hUnmask.trans hCut
  exact ⟨h0, hEnd, hFull.trans hLink, hFull.trans hGrid⟩
