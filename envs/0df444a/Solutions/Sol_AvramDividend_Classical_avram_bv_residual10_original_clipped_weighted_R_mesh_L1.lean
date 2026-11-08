-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_clipped_weighted_R_mesh_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:39:48.800198+00:00
-- url     : https://prove2.me/submissions/e04e9189-d854-4189-9139-8ab84c408a53

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_coordinatewise_weighted_R_mesh_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite clipping turns measurable, possibly unbounded original-process
grid coefficients into a genuinely integrable residual approximant. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (hu0 : u n 0 = 0) (huT : u n (n + 1) ≤ T)
    (a : Ω → ℕ → ℝ)
    (hMeasA : ∀ i, Measurable (fun ω => a ω i))
    (K : ℝ) (hK : 0 ≤ K) :
    Integrable (fun ω =>
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)
      ∑ i ∈ Finset.range (n + 1),
        (if |a ω i| ≤ K then a ω i else 0) *
          (R (u n i) - R (u n (i + 1)))) P := by
  classical
  let aK : Ω → ℕ → ℝ := fun ω i =>
    if |a ω i| ≤ K then a ω i else 0
  change Integrable (fun ω =>
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)
    ∑ i ∈ Finset.range (n + 1),
      aK ω i * (R (u n i) - R (u n (i + 1)))) P
  have hBound : ∀ ω, ∀ i ∈ Finset.range (n + 1),
      |aK ω i| ≤ K := by
    intro ω i hi
    by_cases h : |a ω i| ≤ K
    · simpa [aK, h] using h
    · simp [aK, h, hK]
  have hMeasK : ∀ i,
      AEStronglyMeasurable (fun ω => aK ω i) P := by
    intro i
    have hm : Measurable (fun ω => aK ω i) := by
      dsimp [aK]
      exact Measurable.ite
        (measurableSet_le (hMeasA i).abs measurable_const)
        (hMeasA i) measurable_const
    exact hm.aestronglyMeasurable
  exact avram_bv_residual10_original_coordinatewise_weighted_R_mesh_L1
    X hX hBV T u n hu hu0 huT aK K hK hBound hMeasK
