-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb40_original_bounded_hessian_stopped_weight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:35:06.939921+00:00
-- url     : https://prove2.me/submissions/ad12e009-e8ae-48df-b1fb-1f3a0e009fcc

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_ubv_zerojump_compact_C2_discount_envelope
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original right-continuous stopped Hessian weight is measurable and
bounded uniformly over all deterministic grid times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    ∃ KH : ℝ, 0 ≤ KH ∧ ∀ (t : ℝ≥0) (Y : Ω → ℝ),
      Measurable[𝓕.rightCont t] Y →
      let H : Ω → ℝ := fun ω =>
        if t < ρ ω then (1 / 2 : ℝ) *
          Real.exp (-(q * (t : ℝ))) *
          (if Y ω ∈ Icc a b then iteratedDeriv 2 w (Y ω) else 0)
        else 0
      Measurable H ∧ ∀ ω, |H ω| ≤ KH := by
  classical
  obtain ⟨KG, KH, hKG, hKH, hGB, hHB⟩ :=
    avram_f16_original_ubv_zerojump_compact_C2_discount_envelope
      X hBV hν q hq C w hw_smooth hOpen a b hBand
  have hHess :=
    avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension
      w C hw_smooth
  refine ⟨KH, hKH, ?_⟩
  intro t Y hY
  let H : Ω → ℝ := fun ω =>
    if t < ρ ω then (1 / 2 : ℝ) *
      Real.exp (-(q * (t : ℝ))) *
      (if Y ω ∈ Icc a b then iteratedDeriv 2 w (Y ω) else 0)
    else 0
  change Measurable H ∧ ∀ ω, |H ω| ≤ KH
  have hMask : MeasurableSet[𝓕.rightCont t] {ω : Ω | t < ρ ω} := by
    have he : {ω : Ω | t < ρ ω} =
        {ω : Ω | (ρ ω : WithTop ℝ≥0) ≤ t}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff,
        WithTop.coe_le_coe, not_le]
    rw [he]
    exact (hρstop t).compl
  have hHessian : Measurable (fun y : ℝ =>
      if y ∈ Icc a b then iteratedDeriv 2 w y else 0) := by
    have heq : (fun y : ℝ =>
        if y ∈ Icc a b then iteratedDeriv 2 w y else 0) =
        (fun y => if y ∈ Icc a b then
          (if 0 < y ∧ ENNReal.ofReal y < C
            then iteratedDeriv 2 w y else 0) else 0) := by
      funext y
      by_cases hy : y ∈ Icc a b
      · obtain ⟨hy0, hyC⟩ := hBand hy
        simp [hy, hy0, hyC]
      · simp [hy]
    rw [heq]
    exact Measurable.ite measurableSet_Icc hHess measurable_const
  have hHm : Measurable[𝓕.rightCont t] H := by
    change Measurable[𝓕.rightCont t] (fun ω =>
      if t < ρ ω then (1 / 2 : ℝ) *
        Real.exp (-(q * (t : ℝ))) *
        (if Y ω ∈ Icc a b then iteratedDeriv 2 w (Y ω) else 0)
      else 0)
    exact Measurable.ite hMask
      ((measurable_const.mul measurable_const).mul
        (hHessian.comp hY)) measurable_const
  refine ⟨hHm.mono (𝓕.rightCont.le t) le_rfl, ?_⟩
  intro ω
  by_cases hs : t < ρ ω
  · by_cases hy : Y ω ∈ Icc a b
    · have hh := hHB t (Y ω) hy
      have hhalf :
          |(1 / 2 : ℝ) * (Real.exp (-(q * (t : ℝ))) *
            iteratedDeriv 2 w (Y ω))| ≤ KH := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        nlinarith
      simpa only [H, if_pos hs, if_pos hy] using
        (show |(1 / 2 : ℝ) * Real.exp (-(q * (t : ℝ))) *
            iteratedDeriv 2 w (Y ω)| ≤ KH by
          convert hhalf using 1 <;> ring)
    · simpa only [H, if_pos hs, if_neg hy, mul_zero, abs_zero] using hKH
  · simp [H, hs, hKH]
