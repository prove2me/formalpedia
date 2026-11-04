-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_sigma_quadratic_mesh_error_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:33:45.379541+00:00
-- url     : https://prove2.me/submissions/378d1601-5c77-46dd-83c2-cc7a28844d7f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal
noncomputable section

/-- For refining deterministic time meshes, the source Gaussian quadratic
variation error-variance expression tends to zero. The source stochastic
fourth-moment identification of this expression is a separate obligation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : ℕ → Finset ι) (h : ℕ → ι → ℝ≥0)
    (T : ℝ) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n)
    (hmax : ∀ n, ∀ i ∈ S n, (h n i : ℝ) ≤ ε n)
    (hT : ∀ n, (∑ i ∈ S n, (h n i : ℝ)) ≤ T)
    (hεzero : Tendsto ε atTop (nhds 0)) :
    Tendsto (fun n => (2 : ℝ) * X.σ ^ 4 *
      (∑ i ∈ S n, (h n i : ℝ) ^ 2)) atTop (nhds 0) := by
  have hSig : 0 ≤ (2 : ℝ) * X.σ ^ 4 := by positivity
  have hBounds (n : ℕ) :
      0 ≤ (2 : ℝ) * X.σ ^ 4 *
        (∑ i ∈ S n, (h n i : ℝ) ^ 2) ∧
      (2 : ℝ) * X.σ ^ 4 *
        (∑ i ∈ S n, (h n i : ℝ) ^ 2) ≤
          (2 : ℝ) * X.σ ^ 4 * ε n * T := by
    have hMesh : (∑ i ∈ S n, (h n i : ℝ) ^ 2) ≤
        ε n * (∑ i ∈ S n, (h n i : ℝ)) := by
      calc
        _ ≤ ∑ i ∈ S n, ε n * (h n i : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          have hPos : 0 ≤ (h n i : ℝ) := NNReal.coe_nonneg _
          have hGap : 0 ≤ ε n - (h n i : ℝ) := sub_nonneg.mpr (hmax n i hi)
          nlinarith [mul_nonneg hPos hGap]
        _ = ε n * (∑ i ∈ S n, (h n i : ℝ)) := by rw [Finset.mul_sum]
    constructor
    · exact mul_nonneg hSig (Finset.sum_nonneg (fun i hi => sq_nonneg _))
    · calc
        (2 : ℝ) * X.σ ^ 4 * (∑ i ∈ S n, (h n i : ℝ) ^ 2) ≤
            (2 : ℝ) * X.σ ^ 4 * (ε n * (∑ i ∈ S n, (h n i : ℝ))) :=
          mul_le_mul_of_nonneg_left hMesh hSig
        _ ≤ (2 : ℝ) * X.σ ^ 4 * (ε n * T) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hT n) (hε n)) hSig
        _ = (2 : ℝ) * X.σ ^ 4 * ε n * T := by ring
  have hUpper0 : Tendsto
      (fun n => ((2 : ℝ) * X.σ ^ 4 * T) * ε n)
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        (2 : ℝ) * X.σ ^ 4 * T) atTop
        (nhds ((2 : ℝ) * X.σ ^ 4 * T))).mul hεzero)
  have hUpper : Tendsto (fun n => (2 : ℝ) * X.σ ^ 4 * ε n * T)
      atTop (nhds 0) := by
    convert hUpper0 using 1
    funext n
    ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hUpper (fun n => (hBounds n).1)
      (fun n => (hBounds n).2)
