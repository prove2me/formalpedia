-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb27_original_mapped_finite_clock_discounted_prefix_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:04:52.852251+00:00
-- url     : https://prove2.me/submissions/35ac35e1-87bd-452c-bada-1aa580a0b48a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (q T b : ℝ) (hT : 0 < T) (hb0 : 0 ≤ b) (hbT : b ≤ T) :
    (∫ t : ℝ≥0, (if 0 < t ∧ (t : ℝ) < b then
        Real.exp (-(q * (t : ℝ))) else 0)
      ∂(((volume : Measure ℝ).restrict (Icc (0 : ℝ) T)).map Real.toNNReal)) =
    (∫ t in Ioc (0 : ℝ) b,
      Real.exp (-(q * t)) ∂(volume : Measure ℝ))  := by
  classical
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Icc (0 : ℝ) T)
  let f : ℝ≥0 → ℝ := fun t =>
    if 0 < t ∧ (t : ℝ) < b then Real.exp (-(q * (t : ℝ))) else 0
  have hf : StronglyMeasurable f := by
    have hOne : MeasurableSet {t : ℝ≥0 | 0 < t} := isOpen_Ioi.measurableSet
    have hTwo : MeasurableSet {t : ℝ≥0 | (t : ℝ) < b} :=
      measurableSet_lt measurable_coe_nnreal_real measurable_const
    have hg : Measurable (fun t : ℝ≥0 =>
        Real.exp (-(q * (t : ℝ)))) := by fun_prop
    exact (hg.ite (hOne.inter hTwo) measurable_const).stronglyMeasurable
  have hOn (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      f (Real.toNNReal t) =
        (if t ∈ Ioo (0 : ℝ) b then Real.exp (-(q * t)) else 0) := by
    have hco : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := by
      simp [Real.coe_toNNReal', max_eq_left ht.1]
    have hp : (0 : ℝ≥0) < Real.toNNReal t ↔ 0 < t := by
      rw [← NNReal.coe_lt_coe, NNReal.coe_zero, hco]
    simp only [f, hp, hco, Set.mem_Ioo]
  have hSub : Ioo (0 : ℝ) b ⊆ Icc (0 : ℝ) T := by
    intro t ht
    exact ⟨ht.1.le, ht.2.le.trans hbT⟩
  calc
    (∫ t : ℝ≥0, f t ∂(μ.map Real.toNNReal)) =
      (∫ t : ℝ, f (Real.toNNReal t) ∂μ) :=
        integral_map_of_stronglyMeasurable measurable_real_toNNReal hf
    _ = (∫ t : ℝ, (Ioo (0 : ℝ) b).indicator
          (fun t => Real.exp (-(q * t))) t ∂μ) := by
        apply integral_congr_ae
        have hμ : ∀ᵐ t : ℝ ∂μ, t ∈ Icc (0 : ℝ) T :=
          ae_restrict_mem measurableSet_Icc
        filter_upwards [hμ] with t ht
        simpa only [Set.indicator] using hOn t ht
    _ = (∫ t in Ioo (0 : ℝ) b,
          Real.exp (-(q * t)) ∂μ) := integral_indicator measurableSet_Ioo
    _ = (∫ t in Ioo (0 : ℝ) b,
          Real.exp (-(q * t)) ∂(volume : Measure ℝ)) := by
        have heq : μ.restrict (Ioo (0 : ℝ) b) =
            (volume : Measure ℝ).restrict (Ioo (0 : ℝ) b) := by
          simpa only [μ] using
            (Measure.restrict_restrict_of_subset hSub
              (μ := (volume : Measure ℝ)))
        change (∫ t : ℝ, Real.exp (-(q * t))
            ∂μ.restrict (Ioo (0 : ℝ) b)) =
          (∫ t : ℝ, Real.exp (-(q * t))
            ∂(volume : Measure ℝ).restrict (Ioo (0 : ℝ) b))
        rw [heq]
    _ = _ := (integral_Ioc_eq_integral_Ioo).symm
