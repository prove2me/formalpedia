-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_retained_smallband_exact_variance_20261112
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:22:58.478276+00:00
-- url     : https://prove2.me/submissions/2ec4c19d-d2f5-40f0-bc91-0efada9a0095

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja28_original_bounded_mark_raw_first_second_moments
import Theorems.Thm_AvramDividend_Classical_avram_a21_raw_second_centered_variance_20261112
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Corrected source-exact physical retained-band variance identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      (∫ ω, (avram_p4_h_gaussian_intrinsic_small_band_compensated
        X n t ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in Ioc (-1 : ℝ)
          (-(1 / ((n : ℝ) + 1))), z ^ 2 ∂X.ν) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro n t
  let S : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let J : Ω → ℝ := fun ω =>
    ∫ p in (Ioc 0 t ×ˢ S), p.2 ∂NX ω
  let r : ℝ := (t : ℝ) * (∫ z in S, z ∂X.ν)
  let q : ℝ := (t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν)
  have hBound : ∀ z ∈ Ioc (-(1 / (((0 : ℕ) : ℝ) + 1)))
      (-(1 / ((n : ℝ) + 1))), |z| ≤ 1 := by
    intro z hz
    have hp : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    have hlow : -1 ≤ z := by
      have hh : -1 < z := by simpa using hz.1
      exact le_of_lt hh
    exact abs_le.mpr ⟨by linarith, by linarith [hz.2]⟩
  have hRaw := avram_ja28_original_bounded_mark_raw_first_second_moments
    X hX hFinite 0 n (Nat.zero_le n) (fun z : ℝ => z)
    measurable_id hBound t
  have hMom : Integrable J P ∧
      Integrable (fun ω => (J ω) ^ 2) P ∧
      (∫ ω, J ω ∂P) = r ∧
      (∫ ω, (J ω) ^ 2 ∂P) = r ^ 2 + q := by
    simpa only [Nat.cast_zero, zero_add, one_div_one,
      neg_one_mul, id_eq] using hRaw
  rcases hMom with ⟨hJ, hJ2, hFirst, hSecond⟩
  change (∫ ω, (J ω - r) ^ 2 ∂P) = q
  exact avram_a21_raw_second_centered_variance_20261112
    J r q hJ hJ2 hFirst hSecond
