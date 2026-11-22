-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_deterministic_simple_mark_fibre_quadratic_energy_from_injective_square_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:47:18.360526+00:00
-- url     : https://prove2.me/submissions/18879a51-0d4c-4a5e-a9c3-febd4f91bc2b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a20_spatial_Borel_simple_mark_integral_partition
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (g : SimpleFunc ℝ ℝ)
    (hSqInt : IntegrableOn (fun z : ℝ => (g z) ^ 2) S ν)
    (hInj : ∀ x ∈ g.range, ∀ y ∈ g.range, x ^ 2 = y ^ 2 → x = y)
    (T : ℝ≥0) :
    (∑ y ∈ g.range, y ^ 2 *
      ((T : ℝ≥0∞) * ν (S ∩ g ⁻¹' {y})).toReal) =
      (T : ℝ) * (∫ z in S, (g z) ^ 2 ∂ν)  := by
  classical
  let q : SimpleFunc ℝ ℝ := g.map (fun y => y ^ 2)
  have hqInt : IntegrableOn (fun z : ℝ => q z) S ν := by
    simpa only [q, SimpleFunc.map_apply] using hSqInt
  have hFibre : ∀ y ∈ g.range,
      S ∩ q ⁻¹' {y ^ 2} = S ∩ g ⁻¹' {y} := by
    intro y hy
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, q, SimpleFunc.map_apply]
    constructor
    · rintro ⟨hz, heq⟩
      exact ⟨hz, hInj (g z) (SimpleFunc.mem_range_self g z) y hy heq⟩
    · rintro ⟨hz, heq⟩
      exact ⟨hz, by rw [heq]⟩
  have hSumImage :
      (∑ z ∈ g.range.image (fun y => y ^ 2),
        z * (ν (S ∩ q ⁻¹' {z})).toReal) =
      (∑ y ∈ g.range, y ^ 2 *
        (ν (S ∩ g ⁻¹' {y})).toReal) := by
    rw [Finset.sum_image (by
      intro x hx y hy hxy
      exact hInj x hx y hy hxy)]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hFibre y hy]
  have hSpatial := avram_a20_spatial_Borel_simple_mark_integral_partition
    ν S hS q hqInt
  have hE : (∫ z in S, (g z) ^ 2 ∂ν) =
      ∑ y ∈ g.range, y ^ 2 *
        (ν (S ∩ g ⁻¹' {y})).toReal := by
    change (∫ z in S, q z ∂ν) =
        ∑ z ∈ q.range, z * (ν (S ∩ q ⁻¹' {z})).toReal at hSpatial
    rw [SimpleFunc.range_map] at hSpatial
    exact hSpatial.trans hSumImage
  calc
    (∑ y ∈ g.range, y ^ 2 *
      ((T : ℝ≥0∞) * ν (S ∩ g ⁻¹' {y})).toReal) =
      ∑ y ∈ g.range, (T : ℝ) * (y ^ 2 *
        (ν (S ∩ g ⁻¹' {y})).toReal) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [ENNReal.toReal_mul]
        simp
        ring
    _ = (T : ℝ) *
      (∑ y ∈ g.range, y ^ 2 *
        (ν (S ∩ g ⁻¹' {y})).toReal) := by
          rw [Finset.mul_sum]
    _ = (T : ℝ) * (∫ z in S, (g z) ^ 2 ∂ν) := by rw [hE]
