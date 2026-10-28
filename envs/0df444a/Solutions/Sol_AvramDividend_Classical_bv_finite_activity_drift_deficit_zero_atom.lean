-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_drift_deficit_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:46:31.144733+00:00
-- url     : https://prove2.me/submissions/aeeeeae7-ce13-47d3-aadf-3336489b774a

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_deficit_laplace_nat
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Theorems.Thm_AvramDividend_Classical_nonnegative_laplace_transform_atom_zero_limit_nat
import Theorems.Thm_AvramDividend_Classical_finite_negative_jump_exponential_deficit_limit_nat
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The zero atom of the actual drift deficit has exponential finite-jump survival mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (t : ℝ≥0)
    (hMeas : Measurable (fun ω => X.X t ω)) :
    (∫ ω, if (t : ℝ) * X.drift - X.X t ω = 0 then (1 : ℝ) else 0 ∂P) =
      Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hMeasD : Measurable
      (fun ω => (t : ℝ) * X.drift - X.X t ω) :=
    measurable_const.sub hMeas
  have hNonneg : ∀ᵐ ω ∂P, 0 ≤ (t : ℝ) * X.drift - X.X t ω := by
    filter_upwards [bv_actual_levy_drift_upper_ae_fixed_time X hBV t] with ω hω
    exact sub_nonneg.mpr hω
  have hAtom := nonnegative_laplace_transform_atom_zero_limit_nat
    P (fun ω => (t : ℝ) * X.drift - X.X t ω) hMeasD hNonneg
  have hJump := finite_negative_jump_exponential_deficit_limit_nat X.ν hFinite
  have hArg : Tendsto (fun n : ℕ =>
      -((t : ℝ) *
        ∫ y in Iio (0 : ℝ), (1 - Real.exp ((n : ℝ) * y)) ∂X.ν))
      atTop (𝓝 (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal))) :=
    (tendsto_const_nhds.mul hJump).neg
  have hExp : Tendsto (fun n : ℕ =>
      Real.exp (-((t : ℝ) *
        ∫ y in Iio (0 : ℝ), (1 - Real.exp ((n : ℝ) * y)) ∂X.ν)))
      atTop (𝓝 (Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)))) :=
    (Real.continuous_exp.tendsto _).comp hArg
  have hEq :
      (fun n : ℕ =>
        ∫ ω, Real.exp ((n : ℝ) * (-((t : ℝ) * X.drift - X.X t ω))) ∂P)
        =ᶠ[atTop]
      (fun n : ℕ =>
        Real.exp (-((t : ℝ) *
          ∫ y in Iio (0 : ℝ), (1 - Real.exp ((n : ℝ) * y)) ∂X.ν))) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact bv_actual_levy_drift_deficit_laplace_nat X hBV t n hn
  exact tendsto_nhds_unique_of_eventuallyEq hAtom hExp hEq
