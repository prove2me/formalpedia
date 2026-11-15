-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a311_masked_Gaussian_polynomial_finite_mesh_integrable_from_raw_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:21:34.081201+00:00
-- url     : https://prove2.me/submissions/a47443ad-e78d-47af-82c7-cf6b58026cc0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a310_raw_centered_Gaussian_polynomial_bounded_by_raw_square
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
  let Raw : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range m, if A m i ω then (r m i ω)^2 else 0
  let Poly : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range m,
      if A m i ω ∧ δ ≤ |r m i ω| then
        1 + |r m i ω| + (r m i ω-a m)^2/2 else 0
  have hPm : Measurable Poly := by
    dsimp [Poly]
    apply Finset.measurable_sum
    intro i hi
    have hr := hrm m i
    have hEvent : MeasurableSet
        {ω : Ω | A m i ω ∧ δ ≤ |r m i ω|} := by
      exact (hAm m i).inter ((show MeasurableSet (Set.Ici δ : Set ℝ)
        from measurableSet_Ici).preimage hr.abs)
    exact Measurable.ite hEvent
      ((measurable_const.add hr.abs).add
        (((hr.sub measurable_const).pow_const 2).div_const 2))
      measurable_const
  have hPpos (ω : Ω) : 0 ≤ Poly ω := by
    dsimp [Poly]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  have hPt (ω : Ω) :
      Poly ω ≤ 2*Raw ω+(m : ℝ)*((a m)^2+2) := by
    dsimp [Poly, Raw]
    calc
      _ ≤ ∑ i ∈ Finset.range m,
        (2*(if A m i ω then (r m i ω)^2 else 0)+(a m)^2+2) := by
          apply Finset.sum_le_sum
          intro i hi
          split_ifs with h1 h2
          · simpa [h1, h2] using
              (avram_ga_a310_raw_centered_Gaussian_polynomial_bounded_by_raw_square
                (r m i ω) (a m))
          all_goals simp_all <;> positivity
      _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum] <;> ring
  have hMajor : Integrable (fun ω => 2*Raw ω+(m : ℝ)*((a m)^2+2)) P :=
    ((hRawI m).const_mul 2).add (integrable_const _)
  apply Integrable.mono' hMajor hPm.aestronglyMeasurable
  filter_upwards [] with ω
  have hg : 0 ≤ 2*Raw ω+(m : ℝ)*((a m)^2+2) := by
    have hR : 0 ≤ Raw ω := by
      dsimp [Raw]; apply Finset.sum_nonneg
      intro i hi; split_ifs <;> positivity
    positivity
  simpa only [Real.norm_eq_abs,abs_of_nonneg (hPpos ω),
    abs_of_nonneg hg] using hPt ω
