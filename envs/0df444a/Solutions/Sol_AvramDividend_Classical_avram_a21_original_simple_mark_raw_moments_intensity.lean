-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_simple_mark_raw_moments_intensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T22:34:01.386784+00:00
-- url     : https://prove2.me/submissions/b36b94cd-7047-4561-a020-2931d50bc2cd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_simple_mark_integral_exact_moments
import Theorems.Thm_AvramDividend_Classical_avram_a20_spatial_Borel_simple_mark_integral_partition
import Theorems.Thm_AvramDividend_Classical_avram_a21_finite_simple_mark_quadratic_integral_partition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-- Convert original simple physical mark moments into first and second intensity integrals. -/
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
    let J : Ω → ℝ := fun ω =>
      ∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω
    let r : ℝ := (T : ℝ) * (∫ z in S, g z ∂X.ν)
    let q : ℝ := (T : ℝ) * (∫ z in S, (g z) ^ 2 ∂X.ν)
    Integrable J P ∧ Integrable (fun ω => J ω ^ 2) P ∧
    (∫ ω, J ω ∂P) = r ∧
    (∫ ω, J ω ^ 2 ∂P) = r ^ 2 + q := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let J : Ω → ℝ := fun ω => ∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω
  let r : ℝ := (T : ℝ) * (∫ z in S, g z ∂X.ν)
  let q : ℝ := (T : ℝ) * (∫ z in S, (g z) ^ 2 ∂X.ν)
  change Integrable J P ∧ Integrable (fun ω => J ω ^ 2) P ∧
    (∫ ω, J ω ∂P) = r ∧ (∫ ω, J ω ^ 2 ∂P) = r ^ 2 + q
  let Bf : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
  let mk : ℝ := ∑ y ∈ g.range,
    y * (((T : ℝ≥0∞) * X.ν (Bf y)).toReal)
  let vk : ℝ := ∑ y ∈ g.range,
    y ^ 2 * (((T : ℝ≥0∞) * X.ν (Bf y)).toReal)
  have hSrc : Integrable J P ∧ Integrable (fun ω => J ω ^ 2) P ∧
      (∫ ω, J ω ∂P) = mk ∧ (∫ ω, J ω ^ 2 ∂P) = mk ^ 2 + vk := by
    simpa only [J, NX, Bf, mk, vk] using
      (avram_a20_original_bounded_simple_mark_integral_exact_moments
        X hFinite T S hS hNeg g hBound)
  have hMass : X.ν S < ⊤ :=
    lt_of_le_of_lt (measure_mono hNeg) (lt_top_iff_ne_top.mpr hFinite)
  have hInt : IntegrableOn (fun z : ℝ => g z) S X.ν := by
    apply Measure.integrableOn_of_bounded (ne_of_lt hMass)
      (g.measurable.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem hS] with z hz
    simpa only [Real.norm_eq_abs] using hBound z hz
  have hMk : mk = r := by
    dsimp [mk, Bf, r]
    rw [avram_a20_spatial_Borel_simple_mark_integral_partition X.ν S hS g hInt]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
    ring
  have hVk : vk = q := by
    dsimp [vk, Bf, q]
    rw [avram_a21_finite_simple_mark_quadratic_integral_partition X.ν S hS hMass g]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
    ring
  refine ⟨hSrc.1, hSrc.2.1, hSrc.2.2.1.trans hMk, ?_⟩
  calc
    (∫ ω, J ω ^ 2 ∂P) = mk ^ 2 + vk := hSrc.2.2.2
    _ = r ^ 2 + q := by rw [hMk, hVk]
