-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_coordinatewise_weighted_R_mesh_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:32:11.045118+00:00
-- url     : https://prove2.me/submissions/fee8bba4-2e96-4cf8-8e13-3de7301b5d05

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_original_raw_R_coordinate_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_fixed_time_L1
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_bounded_weighted_R_mesh_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A coordinatewise measurable bounded original-process integrand produces
an L¹ stopped mesh without assuming measurability of the whole sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (hu0 : u n 0 = 0) (huT : u n (n + 1) ≤ T)
    (a : Ω → ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ ω, ∀ i ∈ Finset.range (n + 1), |a ω i| ≤ K)
    (hMeasA : ∀ i, AEStronglyMeasurable (fun ω => a ω i) P) :
    Integrable (fun ω =>
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)
      ∑ i ∈ Finset.range (n + 1),
        a ω i * (R (u n i) - R (u n (i + 1)))) P := by
  classical
  let R : Ω → ℝ≥0 → ℝ := fun ω t =>
    ((t : ℝ) * X.drift - X.X t ω) -
      (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0)
  change Integrable (fun ω =>
    ∑ i ∈ Finset.range (n + 1),
      a ω i * (R ω (u n i) - R ω (u n (i + 1)))) P
  have hInt : Integrable (fun ω => R ω T) P := by
    simpa only [R] using
      (avram_bv_residual10_original_raw_R_fixed_time_L1 X hX hBV T)
  have hCoord (t : ℝ≥0) :
      AEStronglyMeasurable (fun ω => R ω t) P := by
    simpa only [R] using
      (avram_a19_nonint_original_raw_R_coordinate_measurable X hX hBV t)
  have hMeas : AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range (n + 1),
        a ω i * (R ω (u n i) - R ω (u n (i + 1)))) P := by
    have hs : AEStronglyMeasurable
        (∑ i ∈ Finset.range (n + 1), fun ω : Ω =>
          a ω i * (R ω (u n i) - R ω (u n (i + 1)))) P := by
      apply Finset.aestronglyMeasurable_sum
      intro i hi
      exact (hMeasA i).mul ((hCoord (u n i)).sub (hCoord (u n (i + 1))))
    convert hs using 1
    funext ω
    simp only [Finset.sum_apply]
  exact avram_bv_residual10_original_bounded_weighted_R_mesh_L1
    X hBV R (by intro ω t; rfl) T u n hu hu0 huT a K hK hBound hInt hMeas
