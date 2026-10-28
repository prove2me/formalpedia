-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_residual_zero_atom_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:44:35.72985+00:00
-- url     : https://prove2.me/submissions/5babe6d9-ba38-4313-90d1-9587a79c8d84

import Theorems.Thm_AvramDividend_Classical_nonnegative_laplace_transform_atom_zero_limit_nat
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_laplace_tendsto_survival
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Separation.Hausdorff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The actual finite-activity BV Lévy residual has the exact zero-atom survival probability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) :
    P.real {ω : Ω | (t : ℝ) * X.drift - X.X t ω = 0} =
      Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let D : Ω → ℝ := fun ω => (t : ℝ) * X.drift - X.X t ω
  have hMeas : Measurable D :=
    measurable_const.sub (X.adapted.measurable)
  have hNonneg : ∀ᵐ ω ∂P, 0 ≤ D ω := by
    filter_upwards [bv_actual_levy_drift_upper_ae_fixed_time X hBV t] with ω hw
    dsimp [D]
    linarith
  have hAtom := nonnegative_laplace_transform_atom_zero_limit_nat
    P D hMeas hNonneg
  have hLap := bv_actual_residual_laplace_tendsto_survival X hBV hFinite t
  have hLap' : Tendsto
      (fun n : ℕ => ∫ ω, Real.exp ((n : ℝ) * (-D ω)) ∂P)
      atTop (𝓝 (Real.exp (-((t : ℝ) *
        (X.ν (Iio (0 : ℝ))).toReal)))) := by
    simpa only [D, neg_sub] using hLap
  have hUnique := tendsto_nhds_unique hAtom hLap'
  have hs : MeasurableSet {ω : Ω | D ω = 0} := by
    change MeasurableSet (D ⁻¹' {0})
    exact hMeas (measurableSet_singleton 0)
  have hfun :
      (fun ω : Ω => if D ω = 0 then (1 : ℝ) else 0) =
      (fun ω : Ω => ({ω | D ω = 0}).indicator (fun _ => (1 : ℝ)) ω) := by
    funext ω
    simp [Set.indicator_apply]
  have hIntegral :
      (∫ ω, if D ω = 0 then (1 : ℝ) else 0 ∂P) =
        P.real {ω : Ω | D ω = 0} := by
    rw [hfun]
    exact integral_indicator_one hs
  exact hIntegral.symm.trans hUnique
