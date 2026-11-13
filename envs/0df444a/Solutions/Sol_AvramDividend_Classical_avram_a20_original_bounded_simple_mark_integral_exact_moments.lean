-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_bounded_simple_mark_integral_exact_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:16:47.875975+00:00
-- url     : https://prove2.me/submissions/c17cceee-d829-4982-9c23-147c6ce5c103

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_simple_borel_partition_raw_moments
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_finite_activity_negative_jump_count_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
import Theorems.Thm_AvramDividend_Classical_avram_a20_real_simple_mark_integral_partition_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (g : SimpleFunc ℝ ℝ)
    (hBound : ∀ z ∈ S, |g z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    let J : Ω → ℝ := fun ω =>
      ∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω
    let m : ℝ := ∑ y ∈ g.range,
      y * (((T : ℝ≥0∞) * X.ν (B y)).toReal)
    let v : ℝ := ∑ y ∈ g.range,
      y ^ 2 * (((T : ℝ≥0∞) * X.ν (B y)).toReal)
    Integrable J P ∧ Integrable (fun ω => J ω ^ 2) P ∧
      (∫ ω, J ω ∂P) = m ∧
      (∫ ω, J ω ^ 2 ∂P) = m ^ 2 + v := by
  classical
  intro NX B J m v
  let Jsum : Ω → ℝ := fun ω =>
    ∑ y ∈ g.range, y * (NX ω (Ioc 0 T ×ˢ B y)).toReal
  have hMom : Integrable Jsum P ∧
      Integrable (fun ω => Jsum ω ^ 2) P ∧
      (∫ ω, Jsum ω ∂P) = m ∧
      (∫ ω, Jsum ω ^ 2 ∂P) = m ^ 2 + v := by
    simpa only [NX, B, Jsum, m, v] using
      (avram_a20_original_simple_borel_partition_raw_moments
        X hFinite T S hS hNeg g)
  have hAll : ∀ᵐ ω ∂P,
      NX ω (Ioc 0 T ×ˢ Iio (0 : ℝ)) ≠ ⊤ := by
    simpa only [NX] using
      (avram_mix_fin14_original_finite_activity_negative_jump_count_finite_ae
        X hFinite T)
  have hSub :
      Ioc 0 T ×ˢ S ⊆ Ioc 0 T ×ˢ Iio (0 : ℝ) := by
    intro p hp
    exact ⟨hp.1, hNeg hp.2⟩
  have hEq : J =ᵐ[P] Jsum := by
    filter_upwards [hAll] with ω hw
    have hMass : NX ω (Ioc 0 T ×ˢ S) < ⊤ :=
      lt_of_le_of_lt (measure_mono hSub) (lt_top_iff_ne_top.mpr hw)
    have hInt :=
      (avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
        (NX ω) T S hS (fun z => g z) g.measurable
        hMass hBound).1
    simpa only [J, Jsum, B] using
      (avram_a20_real_simple_mark_integral_partition_exact
        (NX ω) T S hS g hInt)
  have hEqSq : (fun ω => J ω ^ 2) =ᵐ[P]
      (fun ω => Jsum ω ^ 2) := by
    filter_upwards [hEq] with ω hw
    rw [hw]
  have hJI : Integrable J P := hMom.1.congr hEq.symm
  have hJ2 : Integrable (fun ω => J ω ^ 2) P :=
    hMom.2.1.congr hEqSq.symm
  refine ⟨hJI, hJ2, ?_, ?_⟩
  · exact (integral_congr_ae hEq).trans hMom.2.2.1
  · exact (integral_congr_ae hEqSq).trans hMom.2.2.2
