-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja27_original_bounded_mark_strip_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:03:14.854089+00:00
-- url     : https://prove2.me/submissions/06b0e271-af41-4cf7-8233-07dcf4ce6b68

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja28_original_bounded_mark_raw_first_second_moments
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Centre physical marked-count raw moments, using explicit integral linearity. -/
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
      let C : Ω → ℝ := fun ω =>
        (∫ p in (Ioc 0 t ×ˢ S), g p.2 ∂NX ω) -
          (t : ℝ) * (∫ z in S, g z ∂X.ν)
      Integrable (fun ω => (C ω) ^ 2) P →
      (∫ ω, (C ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in S, (g z) ^ 2 ∂X.ν) := by
  intro n m hnm g hg hBound t
  let S : Set ℝ :=
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let J : Ω → ℝ := fun ω => ∫ p in (Ioc 0 t ×ˢ S), g p.2 ∂NX ω
  let r : ℝ := (t : ℝ) * (∫ z in S, g z ∂X.ν)
  let q : ℝ := (t : ℝ) * (∫ z in S, (g z) ^ 2 ∂X.ν)
  change Integrable (fun ω => (J ω - r) ^ 2) P →
    (∫ ω, (J ω - r) ^ 2 ∂P) = q
  intro hInt
  haveI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨hJ, hJ2, hMean, hSecond⟩ :=
    avram_ja28_original_bounded_mark_raw_first_second_moments
      X hX hFinite n m hnm g hg hBound t
  change Integrable J P at hJ
  change Integrable (fun ω => (J ω) ^ 2) P at hJ2
  change (∫ ω, J ω ∂P) = r at hMean
  change (∫ ω, (J ω) ^ 2 ∂P) = r ^ 2 + q at hSecond
  have hMul : Integrable (fun ω => 2 * r * J ω) P :=
    hJ.const_mul _
  calc
    (∫ ω, (J ω - r) ^ 2 ∂P) =
        ∫ ω, ((J ω) ^ 2 - 2 * r * J ω) + r ^ 2 ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          ring
    _ = (∫ ω, (J ω) ^ 2 - 2 * r * J ω ∂P) +
          (∫ _ : Ω, (r ^ 2 : ℝ) ∂P) := by
          exact integral_add (hJ2.sub hMul) (integrable_const _)
    _ = (∫ ω, (J ω) ^ 2 ∂P) -
          (∫ ω, 2 * r * J ω ∂P) + r ^ 2 := by
          rw [integral_sub hJ2 hMul]
          simp
    _ = (∫ ω, (J ω) ^ 2 ∂P) -
          2 * r * (∫ ω, J ω ∂P) + r ^ 2 := by
          rw [integral_const_mul]
    _ = q := by
          rw [hMean, hSecond]
          ring
