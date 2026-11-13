-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_bounded_borel_mark_centered_isometry_20261112
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:41:31.33447+00:00
-- url     : https://prove2.me/submissions/cd4b6138-9e11-4538-ae3f-d751a6dc8cb2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja28_original_bounded_mark_raw_first_second_moments
import Theorems.Thm_AvramDividend_Classical_avram_a21_raw_second_centered_variance_20261112
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Physical original marked-jump compensated L2 isometry for bounded Borel marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n m : ℕ), n ≤ m → ∀ (g : ℝ → ℝ),
      Measurable g →
      (∀ z ∈ Ioc (-(1 / ((n : ℝ) + 1)))
        (-(1 / ((m : ℝ) + 1))), |g z| ≤ 1) →
      ∀ (t : ℝ≥0),
      let S : Set ℝ :=
        Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let J : Ω → ℝ := fun ω =>
        ∫ p in (Ioc 0 t ×ˢ S), g p.2 ∂NX ω
      let r : ℝ := (t : ℝ) * (∫ z in S, g z ∂X.ν)
      let q : ℝ := (t : ℝ) * (∫ z in S, (g z) ^ 2 ∂X.ν)
      Integrable (fun ω => (J ω - r) ^ 2) P ∧
        (∫ ω, (J ω - r) ^ 2 ∂P) = q := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro n m hnm g hg hgBound t
  let S : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let J : Ω → ℝ := fun ω => ∫ p in (Ioc 0 t ×ˢ S), g p.2 ∂NX ω
  let r : ℝ := (t : ℝ) * (∫ z in S, g z ∂X.ν)
  let q : ℝ := (t : ℝ) * (∫ z in S, (g z) ^ 2 ∂X.ν)
  change Integrable (fun ω => (J ω - r) ^ 2) P ∧
    (∫ ω, (J ω - r) ^ 2 ∂P) = q
  have hRaw :=
    avram_ja28_original_bounded_mark_raw_first_second_moments
      X hX hFinite n m hnm g hg hgBound t
  change Integrable J P ∧ Integrable (fun ω => (J ω) ^ 2) P ∧
    (∫ ω, J ω ∂P) = r ∧
    (∫ ω, (J ω) ^ 2 ∂P) = r ^ 2 + q at hRaw
  rcases hRaw with ⟨hJ, hJ2, hMean, hSecond⟩
  have hCenterSq : Integrable (fun ω => (J ω - r) ^ 2) P := by
    have hLinear : Integrable (fun ω => 2 * r * J ω) P :=
      hJ.const_mul _
    have hConst : Integrable (fun _ : Ω => r ^ 2) P :=
      integrable_const _
    have hEq : (fun ω => (J ω - r) ^ 2) =
        (fun ω => (J ω) ^ 2 - 2 * r * J ω + r ^ 2) := by
      funext ω
      ring
    rw [hEq]
    exact (hJ2.sub hLinear).add hConst
  exact ⟨hCenterSq, avram_a21_raw_second_centered_variance_20261112
    J r q hJ hJ2 hMean hSecond⟩
