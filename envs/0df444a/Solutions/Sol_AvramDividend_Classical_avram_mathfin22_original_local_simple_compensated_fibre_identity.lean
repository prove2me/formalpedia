-- Prove2me | solution 1 for AvramDividend.Classical.avram_mathfin22_original_local_simple_compensated_fibre_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:19:34.614244+00:00
-- url     : https://prove2.me/submissions/0b807a7f-9049-48e6-abdc-d66707f175a1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_local_simple_mark_fibre_integral_exact
import Theorems.Thm_AvramDividend_Classical_avram_a21_finite_borel_simple_mark_intensity_fibre_sum_20261112
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (S : Set ℝ)
    (hS : MeasurableSet S)
    (hSep : S ⊆ Iic (-(1 / ((n : ℝ) + 1))))
    (g : SimpleFunc ℝ ℝ) (hBound : ∀ z ∈ S, |g z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    ∀ ω,
      (∑ y ∈ g.range, y *
          ((NX ω (Ioc 0 T ×ˢ B y)).toReal -
            (((T : ℝ≥0∞) * X.ν (B y)).toReal))) =
        (∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω) -
          (T : ℝ) * (∫ z in S, g z ∂X.ν) := by
  classical
  intro NX B ω
  have hε : 0 < (1 / ((n : ℝ) + 1)) := by positivity
  have hMass : X.ν S < ⊤ :=
    avram_p2_a_zero_rate_separated_borel_nu_finite
      X S hS (1 / ((n : ℝ) + 1)) hε hSep
  have hRate :=
    avram_a21_finite_borel_simple_mark_intensity_fibre_sum_20261112
      X.ν T S hS hMass g hBound
  have hPath :=
    avram_mathfin22_original_local_simple_mark_fibre_integral_exact
      X T n S hS hSep g hBound
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
          rw [← hPath ω, hRate]
