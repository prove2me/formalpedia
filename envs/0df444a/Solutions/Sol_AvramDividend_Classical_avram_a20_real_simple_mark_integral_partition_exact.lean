-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_real_simple_mark_integral_partition_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:07:59.541009+00:00
-- url     : https://prove2.me/submissions/8774b4c7-a9c4-4e8a-b5d4-14d35f9ddb42

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    (μ : Measure (ℝ≥0 × ℝ)) (t : ℝ≥0)
    (S : Set ℝ) (hS : MeasurableSet S)
    (g : SimpleFunc ℝ ℝ)
    (hInt : IntegrableOn (fun p : ℝ≥0 × ℝ => g p.2)
      (Ioc 0 t ×ˢ S) μ) :
    (∫ p in (Ioc 0 t ×ˢ S), g p.2 ∂μ) =
      ∑ y ∈ g.range, y *
        (μ (Ioc 0 t ×ˢ (S ∩ g ⁻¹' {y}))).toReal := by
  classical
  let C : Set (ℝ≥0 × ℝ) := Ioc 0 t ×ˢ S
  let f : SimpleFunc (ℝ≥0 × ℝ) ℝ :=
    g.comp Prod.snd measurable_snd
  have hf (p : ℝ≥0 × ℝ) : f p = g p.2 := rfl
  have hRange : f.range = g.range := by
    apply Finset.ext
    intro y
    simp only [SimpleFunc.mem_range, Set.mem_range]
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨p.2, hp⟩
    · rintro ⟨z, hz⟩
      exact ⟨((0 : ℝ≥0), z), hz⟩
  have hFInt : Integrable (fun p => f p) (μ.restrict C) := by
    change IntegrableOn (fun p : ℝ≥0 × ℝ => g p.2)
      (Ioc 0 t ×ˢ S) μ
    exact hInt
  have hSet (y : ℝ) :
      (f ⁻¹' {y}) ∩ C =
        Ioc 0 t ×ˢ (S ∩ g ⁻¹' {y}) := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff,
      Set.mem_prod, C, hf]
    tauto
  have hFormula :=
    SimpleFunc.integral_eq_sum f hFInt
  calc
    (∫ p in (Ioc 0 t ×ˢ S), g p.2 ∂μ) =
        (∫ p, f p ∂(μ.restrict C)) := by
      congr 1
    _ = ∑ y ∈ f.range, (μ.restrict C).real (f ⁻¹' {y}) • y :=
      hFormula
    _ = ∑ y ∈ g.range, y *
          (μ (Ioc 0 t ×ˢ (S ∩ g ⁻¹' {y}))).toReal := by
      rw [hRange]
      apply Finset.sum_congr rfl
      intro y hy
      rw [Measure.real_def]
      rw [Measure.restrict_apply (f.measurableSet_fiber y), hSet y]
      simp only [smul_eq_mul]
      ring
