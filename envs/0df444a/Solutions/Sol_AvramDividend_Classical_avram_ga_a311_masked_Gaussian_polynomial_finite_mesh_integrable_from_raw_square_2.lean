-- Prove2me | solution 2 for AvramDividend.Classical.avram_ga_a311_masked_Gaussian_polynomial_finite_mesh_integrable_from_raw_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:22:35.801126+00:00
-- url     : https://prove2.me/submissions/ce425b92-08e8-4248-ae3b-9165e1d31828

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a330_integrable_nonnegative_finite_sum_implies_integrable_each_measurable_cell
import Theorems.Thm_AvramDividend_Classical_avram_ga_a331_one_masked_Gaussian_rare_polynomial_integrable_of_raw_square
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (r : ℕ → ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (A : ℕ → ℕ → Ω → Prop)
    [∀ m i, DecidablePred (A m i)]
    (δ : ℝ) (hδ : 0 < δ)
    (hrm : ∀ m i, Measurable (r m i))
    (hAm : ∀ m i, MeasurableSet {ω : Ω | A m i ω})
    (hRawI : ∀ m, Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if A m i ω then (r m i ω)^2 else 0) P) :
    ∀ m, Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if A m i ω ∧ δ ≤ |r m i ω| then
          1 + |r m i ω| + (r m i ω-a m)^2/2 else 0) P := by
  intro m
  let raw : ℕ → Ω → ℝ := fun i ω =>
    if A m i ω then (r m i ω)^2 else 0
  have hMeas (i : ℕ) (hi : i ∈ Finset.range m) :
      Measurable (raw i) := by
    exact Measurable.ite (hAm m i)
      ((hrm m i).pow_const 2) measurable_const
  have hPos (i : ℕ) (hi : i ∈ Finset.range m)
      (ω : Ω) : 0 ≤ raw i ω := by
    dsimp [raw]
    split_ifs <;> positivity
  have hEach := avram_ga_a330_integrable_nonnegative_finite_sum_implies_integrable_each_measurable_cell
    P (Finset.range m) raw hMeas hPos
    (by simpa only [raw] using hRawI m)
  apply integrable_finset_sum
  intro i hi
  exact avram_ga_a331_one_masked_Gaussian_rare_polynomial_integrable_of_raw_square
    P (r m i) (a m) δ (A m i) (hAm m i) (hrm m i)
    (hEach i hi)
