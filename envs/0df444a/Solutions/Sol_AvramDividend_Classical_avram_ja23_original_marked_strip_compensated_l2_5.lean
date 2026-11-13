-- Prove2me | solution 5 for AvramDividend.Classical.avram_ja23_original_marked_strip_compensated_l2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T22:44:16.312204+00:00
-- url     : https://prove2.me/submissions/e6d64c07-99cb-4742-bc11-f3f38be661d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja28_original_bounded_mark_raw_first_second_moments

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Direct original-space second moment of the physical marked strip from raw bounded moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n m : ℕ), n ≤ m → ∀ (t : ℝ≥0),
      let S : Set ℝ :=
        Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let C : Ω → ℝ := fun ω =>
        (∫ p in (Ioc 0 t ×ˢ S), p.2 ∂NX ω) -
          (t : ℝ) * (∫ z in S, z ∂X.ν)
      Integrable (fun ω => (C ω) ^ 2) P ∧
      (∫ ω, (C ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν) := by
  intro n m hnm t
  let S : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let J : Ω → ℝ := fun ω => ∫ p in (Ioc 0 t ×ˢ S), p.2 ∂NX ω
  let r : ℝ := (t : ℝ) * (∫ z in S, z ∂X.ν)
  let q : ℝ := (t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν)
  change Integrable (fun ω => (J ω - r) ^ 2) P ∧
    (∫ ω, (J ω - r) ^ 2 ∂P) = q
  letI : IsProbabilityMeasure P := X.isProbability
  have hBound : ∀ z ∈ S, |z| ≤ 1 := by
    intro z hz
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden : 0 < (n : ℝ) + 1 := by linarith
    have hfrac : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ hden).2
      linarith
    have hm : 0 < (m : ℝ) + 1 := by positivity
    have hpos : 0 < (1 : ℝ) / ((m : ℝ) + 1) := by positivity
    apply abs_le.mpr
    constructor
    · exact le_trans (by linarith : -1 ≤ -(1 / ((n : ℝ) + 1))) (le_of_lt hz.1)
    · exact le_trans hz.2 (by linarith : -(1 / ((m : ℝ) + 1)) ≤ 1)
  obtain ⟨hJ, hJ2, hMean, hSecond⟩ :=
    avram_ja28_original_bounded_mark_raw_first_second_moments
      X hX hFinite n m hnm (fun z : ℝ => z) measurable_id
      (by simpa only [S] using hBound) t
  change Integrable J P at hJ
  change Integrable (fun ω => (J ω) ^ 2) P at hJ2
  change (∫ ω, J ω ∂P) = r at hMean
  change (∫ ω, (J ω) ^ 2 ∂P) = r ^ 2 + q at hSecond
  have hMul : Integrable (fun ω => (2 * r) * J ω) P := hJ.const_mul _
  have hPoly : Integrable (fun ω => (J ω) ^ 2 - (2 * r) * J ω + r ^ 2) P :=
    (hJ2.sub hMul).add (integrable_const _)
  have hEq : (fun ω => (J ω - r) ^ 2) =
      (fun ω => (J ω) ^ 2 - (2 * r) * J ω + r ^ 2) := by
    funext ω
    ring
  have hC : Integrable (fun ω => (J ω - r) ^ 2) P := by
    rw [hEq]
    exact hPoly
  have hMemLp : MemLp J 2 P :=
    (memLp_two_iff_integrable_sq hJ.aestronglyMeasurable).2 hJ2
  refine ⟨hC, ?_⟩
  calc
    (∫ ω, (J ω - r) ^ 2 ∂P) = ProbabilityTheory.variance J P := by
      rw [ProbabilityTheory.variance_eq_integral
        hJ.aestronglyMeasurable.aemeasurable, hMean]
    _ = (∫ ω, (J ω) ^ 2 ∂P) - (∫ ω, J ω ∂P) ^ 2 := by
      simpa only [Pi.pow_apply] using
        (ProbabilityTheory.variance_eq_sub hMemLp)
    _ = q := by rw [hMean, hSecond]; ring
