-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_deficit_ae_positive_time_cauchy_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:20:34.911911+00:00
-- url     : https://prove2.me/submissions/12af248b-1cb8-4d20-8e94-995f8efea6a3

import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.UniformSpace.Cauchy
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        CauchySeq (fun n : ℕ =>
          ((X.drift * (Real.toNNReal (t + ((1 : ℝ) / 2) ^ n) : ℝ) -
                X.X (Real.toNNReal (t + ((1 : ℝ) / 2) ^ n)) ω) -
              (X.drift * (Real.toNNReal t : ℝ) -
                X.X (Real.toNNReal t) ω)) / ((1 : ℝ) / 2) ^ n) := by
  have hStep : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n)
      atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_pow_atTop_nhdsWithin_zero_of_lt_one
      (by norm_num) (by norm_num)
  filter_upwards [bv_drift_deficit_ae_monotone_all_times X hBV]
    with ω hMono
  let S : ℝ≥0 → ℝ := fun s => X.drift * (s : ℝ) - X.X s ω
  let f : ℝ → ℝ := fun t => S (Real.toNNReal t)
  have hf : Monotone f := hMono.comp Real.toNNReal_monotone
  have hReal : ∀ᵐ t : ℝ ∂volume,
      CauchySeq (fun n : ℕ =>
        (f (t + ((1 : ℝ) / 2) ^ n) - f t) /
          ((1 : ℝ) / 2) ^ n) := by
    filter_upwards [hf.ae_differentiableAt] with t hDiff
    have hRight :=
      hDiff.hasDerivAt.tendsto_slope_zero_right.comp hStep
    have hSequence :
        (fun n : ℕ =>
          (f (t + ((1 : ℝ) / 2) ^ n) - f t) /
            ((1 : ℝ) / 2) ^ n) =
        (fun n : ℕ =>
          (((1 : ℝ) / 2) ^ n)⁻¹ •
            (f (t + ((1 : ℝ) / 2) ^ n) - f t)) := by
      funext n
      simp only [smul_eq_mul, div_eq_mul_inv]
      ring
    rw [hSequence]
    exact hRight.cauchySeq
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hReal] with t ht _
  simpa only [f, S] using ht
