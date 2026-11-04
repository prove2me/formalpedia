-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_sigma_fourth_moment_mesh_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:33:41.287287+00:00
-- url     : https://prove2.me/submissions/0ef4f3fc-a5c7-4c7e-92ad-ba37f46076c4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The exact Gaussian fourth-moment mesh-error coefficient vanishes at least
linearly in mesh width. It is source-specific through X.σ; an independent
Gaussian fourth-moment/covariance theorem is needed to identify this bound
with the actual quadratic-variation error on the original process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ι) (h : ι → ℝ≥0) (T ε : ℝ)
    (hε : 0 ≤ ε)
    (hmax : ∀ i ∈ S, (h i : ℝ) ≤ ε)
    (hT : (∑ i ∈ S, (h i : ℝ)) ≤ T) :
    0 ≤ (2 : ℝ) * X.σ ^ 4 * (∑ i ∈ S, (h i : ℝ) ^ 2) ∧
    (2 : ℝ) * X.σ ^ 4 * (∑ i ∈ S, (h i : ℝ) ^ 2) ≤
      (2 : ℝ) * X.σ ^ 4 * ε * T := by
  have hSigma : 0 ≤ (2 : ℝ) * X.σ ^ 4 := by positivity
  have hSquare : 0 ≤ (∑ i ∈ S, (h i : ℝ) ^ 2) :=
    Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hMesh : (∑ i ∈ S, (h i : ℝ) ^ 2) ≤
      ε * (∑ i ∈ S, (h i : ℝ)) := by
    calc
      _ ≤ ∑ i ∈ S, ε * (h i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hnonneg : 0 ≤ (h i : ℝ) := NNReal.coe_nonneg _
        have hbound : 0 ≤ ε - (h i : ℝ) := sub_nonneg.mpr (hmax i hi)
        nlinarith [mul_nonneg hnonneg hbound]
      _ = ε * (∑ i ∈ S, (h i : ℝ)) := by rw [Finset.mul_sum]
  constructor
  · exact mul_nonneg hSigma hSquare
  · calc
      (2 : ℝ) * X.σ ^ 4 * (∑ i ∈ S, (h i : ℝ) ^ 2) ≤
          (2 : ℝ) * X.σ ^ 4 * (ε * (∑ i ∈ S, (h i : ℝ))) :=
        mul_le_mul_of_nonneg_left hMesh hSigma
      _ ≤ (2 : ℝ) * X.σ ^ 4 * (ε * T) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hT hε) hSigma
      _ = (2 : ℝ) * X.σ ^ 4 * ε * T := by ring
