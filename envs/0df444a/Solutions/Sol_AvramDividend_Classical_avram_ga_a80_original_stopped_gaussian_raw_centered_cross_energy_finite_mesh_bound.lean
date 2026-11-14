-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a80_original_stopped_gaussian_raw_centered_cross_energy_finite_mesh_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:58:46.209195+00:00
-- url     : https://prove2.me/submissions/957a5176-7906-4e16-82eb-ad7faf5aaff7

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a79_original_gaussian_raw_centered_quadratic_cross_young
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The actual pre-stop Gaussian physical raw-centred quadratic cross error is bounded by a small centred-energy fraction plus deterministic drift-squared mesh mass. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (S : Finset ℕ) (s : ℕ → ℝ≥0)
    (ρ : Ω → ℝ≥0) (ω : Ω)
    (Z : ℕ → ℝ) (d ε : ℝ) (hε : 0 < ε) :
    (∑ i ∈ S, if s i < ρ ω then
      |(Z i + d)^2 - (Z i)^2| else 0) ≤
        ε * (∑ i ∈ S, if s i < ρ ω then (Z i)^2 else 0) +
        (S.card : ℝ) * ((1 + 1 / ε) * d^2) := by
  classical
  have hPoint (i : ℕ) (hi : i ∈ S) :
      (if s i < ρ ω then |(Z i + d)^2 - (Z i)^2| else 0) ≤
        ε * (if s i < ρ ω then (Z i)^2 else 0) +
          (1 + 1 / ε) * d^2 := by
    by_cases h : s i < ρ ω
    · simp only [if_pos h]
      exact avram_ga_a79_original_gaussian_raw_centered_quadratic_cross_young
        (Z i) d ε hε
    · simp only [if_neg h, mul_zero, zero_add]
      have hInv : 0 ≤ 1 / ε := one_div_nonneg.mpr hε.le
      exact mul_nonneg (by linarith) (sq_nonneg _)
  calc
    (∑ i ∈ S, if s i < ρ ω then
      |(Z i + d)^2 - (Z i)^2| else 0) ≤
        ∑ i ∈ S, (ε *
          (if s i < ρ ω then (Z i)^2 else 0) +
          (1 + 1 / ε) * d^2) :=
      Finset.sum_le_sum hPoint
    _ = ε * (∑ i ∈ S, if s i < ρ ω then
          (Z i)^2 else 0) +
          (S.card : ℝ) * ((1 + 1 / ε) * d^2) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul] <;> ring
