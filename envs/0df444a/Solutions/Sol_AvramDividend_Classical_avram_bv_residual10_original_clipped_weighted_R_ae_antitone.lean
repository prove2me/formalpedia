-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_clipped_weighted_R_ae_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:48:07.523452+00:00
-- url     : https://prove2.me/submissions/9c467d79-ec17-4fc9-99c6-73e4bbaa2569

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_ae_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Clipping larger nonnegative weights makes each original BV residual grid
sum more negative. This is the monotonicity needed for a Fatou limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (a : Ω → ℕ → ℝ)
    (ha : ∀ ω, ∀ i ∈ Finset.range (n + 1), 0 ≤ a ω i)
    (k l : ℝ) (hkl : k ≤ l) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range (n + 1),
        (if |a ω i| ≤ l then a ω i else 0) *
          (R (u n i) - R (u n (i + 1)))) ≤
      (∑ i ∈ Finset.range (n + 1),
        (if |a ω i| ≤ k then a ω i else 0) *
          (R (u n i) - R (u n (i + 1)))) := by
  classical
  filter_upwards [avram_bv_residual10_original_raw_R_ae_monotone X hBV]
    with ω hmono
  let R : ℝ≥0 → ℝ := fun t =>
    ((t : ℝ) * X.drift - X.X t ω) -
      (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0)
  change (∑ i ∈ Finset.range (n + 1),
      (if |a ω i| ≤ l then a ω i else 0) *
        (R (u n i) - R (u n (i + 1)))) ≤
    (∑ i ∈ Finset.range (n + 1),
      (if |a ω i| ≤ k then a ω i else 0) *
        (R (u n i) - R (u n (i + 1))))
  apply Finset.sum_le_sum
  intro i hi
  have hdec : R (u n i) - R (u n (i + 1)) ≤ 0 :=
    sub_nonpos.mpr (hmono (hu i (Finset.mem_range.mp hi)))
  have hpos : 0 ≤ a ω i := ha ω i hi
  have hcoeff :
      (if |a ω i| ≤ k then a ω i else 0) ≤
        (if |a ω i| ≤ l then a ω i else 0) := by
    by_cases hk : |a ω i| ≤ k
    · have hl : |a ω i| ≤ l := hk.trans hkl
      simp [hk, hl]
    · by_cases hl : |a ω i| ≤ l
      · simpa [hk, hl] using hpos
      · simp [hk, hl]
  exact mul_le_mul_of_nonpos_right hcoeff hdec
