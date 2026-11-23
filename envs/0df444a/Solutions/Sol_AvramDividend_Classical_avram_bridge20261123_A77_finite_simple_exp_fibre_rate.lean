-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A77_finite_simple_exp_fibre_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T16:38:55.716785+00:00
-- url     : https://prove2.me/submissions/5e58961e-13e3-41e7-bb65-5998aae1ebed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) ≠ ⊤)
    (g : SimpleFunc ℝ ℝ) :
    (∫ y in Iio (0 : ℝ), Real.exp (g y) - 1 ∂ν) =
      ∑ z ∈ g.range,
        (ν (Iio (0 : ℝ) ∩ g ⁻¹' {z})).toReal *
          (Real.exp z - 1) := by
  classical
  let μ := ν.restrict (Iio (0 : ℝ))
  haveI : IsFiniteMeasure μ := by
    exact isFiniteMeasure_restrict.mpr hFinite
  let φ : ℝ → ℝ := fun z => Real.exp z - 1
  have hφ : φ 0 = 0 := by simp [φ]
  have hInt : Integrable g μ :=
    SimpleFunc.integrable_of_isFiniteMeasure g
  have hMapInt : Integrable (g.map φ) μ :=
    SimpleFunc.integrable_of_isFiniteMeasure _
  calc
    (∫ y in Iio (0 : ℝ), Real.exp (g y) - 1 ∂ν) =
        ∫ y, (g.map φ) y ∂μ := by rfl
    _ = (g.map φ).integral μ :=
      (SimpleFunc.integral_eq_integral _ hMapInt).symm
    _ = ∑ z ∈ g.range, (μ.real (g ⁻¹' {z})) • φ z :=
      SimpleFunc.map_integral g φ hInt hφ
    _ = ∑ z ∈ g.range,
        (ν (Iio (0 : ℝ) ∩ g ⁻¹' {z})).toReal *
          (Real.exp z - 1) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [smul_eq_mul, measureReal_def]
      rw [Measure.restrict_apply (g.measurableSet_preimage _)]
      simpa only [φ, Set.inter_comm]
