-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_bounded_compensated_mark_ae_count_rate_domination_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:29:06.4162+00:00
-- url     : https://prove2.me/submissions/5c8141dd-4934-44ac-9f35-52a64a1f901f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_mark_integral_ae_count_domination
import Theorems.Thm_AvramDividend_Classical_avram_a21_finite_borel_mark_real_intensity_norm_bound_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original physical compensated bounded Borel mark integral
is dominated by its true negative mark count plus the source intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (f : ℝ → ℝ) (hf : Measurable f)
    (hBound : ∀ z ∈ S, |f z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let N : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ S)).toReal
    let r : ℝ := ((T : ℝ≥0∞) * X.ν S).toReal
    ∀ᵐ ω ∂P,
      ‖(∫ p in (Ioc 0 T ×ˢ S), f p.2 ∂NX ω) -
        (T : ℝ) * (∫ z in S, f z ∂X.ν)‖ ≤ N ω + r := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let N : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ S)).toReal
  let r : ℝ := ((T : ℝ≥0∞) * X.ν S).toReal
  have hMass : X.ν S < ⊤ :=
    lt_of_le_of_lt (measure_mono hNeg)
      (lt_top_iff_ne_top.mpr hFinite)
  have hSourceBound :=
    avram_a21_finite_borel_mark_real_intensity_norm_bound_20261113
      X.ν S hS hMass f hBound
  have ht : (T : ℝ≥0∞).toReal = (T : ℝ) := by simp
  have hComp : ‖(T : ℝ) * (∫ z in S, f z ∂X.ν)‖ ≤ r := by
    rw [norm_mul, Real.norm_eq_abs]
    have hT : |(T : ℝ)| = (T : ℝ) := abs_of_nonneg (by positivity)
    rw [hT]
    calc
      (T : ℝ) * ‖∫ z in S, f z ∂X.ν‖ ≤
        (T : ℝ) * (X.ν S).toReal :=
          mul_le_mul_of_nonneg_left hSourceBound (by positivity)
      _ = r := by simp only [r, ENNReal.toReal_mul, ht]
  have hPhysical :=
    avram_a20_original_bounded_mark_integral_ae_count_domination
      X hFinite T S hS hNeg f hf hBound
  filter_upwards [hPhysical] with ω hω
  change ‖(∫ p in (Ioc 0 T ×ˢ S), f p.2 ∂NX ω) -
    (T : ℝ) * (∫ z in S, f z ∂X.ν)‖ ≤ N ω + r
  calc
    _ ≤ ‖(∫ p in (Ioc 0 T ×ˢ S), f p.2 ∂NX ω)‖ +
      ‖(T : ℝ) * (∫ z in S, f z ∂X.ν)‖ := norm_sub_le _ _
    _ ≤ N ω + r := add_le_add (by
      simpa only [Real.norm_eq_abs, N] using hω.2) hComp
