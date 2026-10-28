-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_deficit_laplace_integrability_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T14:17:14.944021+00:00
-- url     : https://prove2.me/submissions/c8092913-5f7d-46b4-8015-c3b2d300a980

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Finite measure and a nonnegative measurable deficit control all three Laplace-gap kernels. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (D : Ω → ℝ) (hD : Measurable D)
    (hNonneg : ∀ᵐ ω ∂μ, 0 ≤ D ω)
    (n a : ℝ) (hn : 0 ≤ n) :
    MeasurableSet {ω : Ω | 0 < D ω ∧ n * D ω ≤ a} ∧
    MeasurableSet {ω : Ω | D ω = 0} ∧
    Integrable (fun ω => if 0 < D ω ∧ n * D ω ≤ a then (1 : ℝ) else 0) μ ∧
    Integrable (fun ω => if D ω = 0 then (0 : ℝ) else Real.exp (-(n * D ω))) μ ∧
    Integrable (fun ω => if D ω = 0 then (1 : ℝ) else 0) μ := by
  have hs : MeasurableSet {ω : Ω | 0 < D ω ∧ n * D ω ≤ a} :=
    (measurableSet_lt measurable_const hD).inter
      (measurableSet_le (measurable_const.mul hD) measurable_const)
  have hz : MeasurableSet {ω : Ω | D ω = 0} :=
    hD (show MeasurableSet {z : ℝ | z = 0} from measurableSet_eq)
  have hL : Measurable
      (fun ω => if 0 < D ω ∧ n * D ω ≤ a then (1 : ℝ) else 0) :=
    Measurable.ite hs measurable_const measurable_const
  have hZ : Measurable
      (fun ω => if D ω = 0 then (1 : ℝ) else 0) :=
    Measurable.ite hz measurable_const measurable_const
  have hExp : Measurable (fun ω => Real.exp (-(n * D ω))) :=
    Real.measurable_exp.comp ((measurable_const.mul hD).neg)
  have hR : Measurable
      (fun ω => if D ω = 0 then (0 : ℝ) else Real.exp (-(n * D ω))) :=
    Measurable.ite hz measurable_const hExp
  refine ⟨hs, hz, ?_, ?_, ?_⟩
  · apply Integrable.of_bound hL.aestronglyMeasurable 1
    filter_upwards [] with ω
    by_cases h : 0 < D ω ∧ n * D ω ≤ a <;> simp [h]
  · apply Integrable.of_bound hR.aestronglyMeasurable 1
    filter_upwards [hNonneg] with ω hω
    by_cases hzero : D ω = 0
    · simp [hzero]
    · simp only [if_neg hzero, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (mul_nonneg hn hω)
  · apply Integrable.of_bound hZ.aestronglyMeasurable 1
    filter_upwards [] with ω
    by_cases hzero : D ω = 0 <;> simp [hzero]
