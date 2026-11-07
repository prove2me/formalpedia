-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:04:14.441678+00:00
-- url     : https://prove2.me/submissions/8da22cc9-7a84-49df-8fe8-eefda76b0e4e

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (μ ν : Measure (ℝ≥0 × ℝ)) (s T : ℝ≥0)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    (hRect : ∀ B : Set ℝ, MeasurableSet B →
      μ (Ioc 0 T ×ˢ B) = ν (Ioc s (s + T) ×ˢ B)) :
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂μ) =
    (∫⁻ p : ℝ≥0 × ℝ,
      if s < p.1 ∧ p.1 ≤ s + T then g p.2 else 0 ∂ν) := by
  let A : Set (ℝ≥0 × ℝ) := Ioc 0 T ×ˢ Set.univ
  let C : Set (ℝ≥0 × ℝ) := Ioc s (s + T) ×ˢ Set.univ
  have hA : MeasurableSet A := measurableSet_Ioc.prod MeasurableSet.univ
  have hC : MeasurableSet C := measurableSet_Ioc.prod MeasurableSet.univ
  let μmark : Measure ℝ := (μ.restrict A).map Prod.snd
  let νmark : Measure ℝ := (ν.restrict C).map Prod.snd
  have hmark : μmark = νmark := by
    apply Measure.ext
    intro E hE
    have hME : MeasurableSet ((Prod.snd : (ℝ≥0 × ℝ) → ℝ) ⁻¹' E) := (measurable_snd : Measurable (Prod.snd : (ℝ≥0 × ℝ) → ℝ)) hE
    have hEA : ((Prod.snd : (ℝ≥0 × ℝ) → ℝ) ⁻¹' E) ∩ A = Ioc 0 T ×ˢ E := by
      ext p
      simp [A, Set.mem_prod, and_comm, and_left_comm, and_assoc]
    have hEC : ((Prod.snd : (ℝ≥0 × ℝ) → ℝ) ⁻¹' E) ∩ C = Ioc s (s + T) ×ˢ E := by
      ext p
      simp [C, Set.mem_prod, and_comm, and_left_comm, and_assoc]
    simpa only [μmark, νmark, Measure.map_apply (measurable_snd : Measurable (Prod.snd : (ℝ≥0 × ℝ) → ℝ)) hE,
      Measure.restrict_apply hME, hEA, hEC] using hRect E hE
  have hleft :
      (∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂μ) =
      ∫⁻ y : ℝ, g y ∂μmark := by
    have hi : (∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂μ) =
        ∫⁻ p : ℝ≥0 × ℝ, A.indicator (fun p => g p.2) p ∂μ := by
      congr 1
      funext p
      simp [A, Set.indicator]
    rw [hi, lintegral_indicator hA]
    exact (lintegral_map hg (measurable_snd : Measurable (Prod.snd : (ℝ≥0 × ℝ) → ℝ))).symm
  have hright :
      (∫⁻ p : ℝ≥0 × ℝ,
        if s < p.1 ∧ p.1 ≤ s + T then g p.2 else 0 ∂ν) =
      ∫⁻ y : ℝ, g y ∂νmark := by
    have hi : (∫⁻ p : ℝ≥0 × ℝ,
        if s < p.1 ∧ p.1 ≤ s + T then g p.2 else 0 ∂ν) =
        ∫⁻ p : ℝ≥0 × ℝ, C.indicator (fun p => g p.2) p ∂ν := by
      congr 1
      funext p
      simp [C, Set.indicator]
    rw [hi, lintegral_indicator hC]
    exact (lintegral_map hg (measurable_snd : Measurable (Prod.snd : (ℝ≥0 × ℝ) → ℝ))).symm
  calc
    _ = ∫⁻ y : ℝ, g y ∂μmark := hleft
    _ = ∫⁻ y : ℝ, g y ∂νmark := by rw [hmark]
    _ = _ := hright.symm
