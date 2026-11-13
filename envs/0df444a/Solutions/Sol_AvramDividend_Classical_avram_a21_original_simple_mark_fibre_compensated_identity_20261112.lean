-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_simple_mark_fibre_compensated_identity_20261112
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:09:14.760108+00:00
-- url     : https://prove2.me/submissions/455c97dc-18fa-4b49-8408-e588644750ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_bounded_mark_pathwise_fibre_partition_20261112
import Theorems.Thm_AvramDividend_Classical_avram_a21_finite_borel_simple_mark_intensity_fibre_sum_20261112
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- True source compensated simple marked integral equals its finite
disjoint fibre-centred count sum, on the original Omega and P. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ)
    (hS : MeasurableSet S) (hNeg : S ⊆ Iio (0 : ℝ))
    (g : SimpleFunc ℝ ℝ) (hBound : ∀ z ∈ S, |g z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    ∀ᵐ ω ∂P,
      (∑ y ∈ g.range, y *
          ((NX ω (Ioc 0 T ×ˢ B y)).toReal -
            (((T : ℝ≥0∞) * X.ν (B y)).toReal))) =
        (∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω) -
          (T : ℝ) * (∫ z in S, g z ∂X.ν) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
  have hMass : X.ν S < ⊤ :=
    lt_of_le_of_lt (measure_mono hNeg)
      (lt_top_iff_ne_top.mpr hFinite)
  have hRate :=
    avram_a21_finite_borel_simple_mark_intensity_fibre_sum_20261112
      X.ν T S hS hMass g hBound
  have hPath :=
    avram_a21_original_simple_bounded_mark_pathwise_fibre_partition_20261112
      X hFinite T S hS hNeg g hBound
  filter_upwards [hPath] with ω hω
  change (∑ y ∈ g.range, y *
      ((NX ω (Ioc 0 T ×ˢ B y)).toReal -
        (((T : ℝ≥0∞) * X.ν (B y)).toReal))) =
      (∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω) -
        (T : ℝ) * (∫ z in S, g z ∂X.ν)
  calc
    (∑ y ∈ g.range, y *
      ((NX ω (Ioc 0 T ×ˢ B y)).toReal -
        (((T : ℝ≥0∞) * X.ν (B y)).toReal))) =
      (∑ y ∈ g.range, y *
        (NX ω (Ioc 0 T ×ˢ B y)).toReal) -
      (∑ y ∈ g.range, y *
        (((T : ℝ≥0∞) * X.ν (B y)).toReal)) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro y hy
          ring
    _ = (∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω) -
        (T : ℝ) * (∫ z in S, g z ∂X.ν) := by
          rw [hω, hRate]
