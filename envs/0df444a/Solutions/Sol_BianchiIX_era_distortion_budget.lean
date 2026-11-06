-- Prove2me | solution 1 for BianchiIX.era_distortion_budget
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:14:39.358974+00:00
-- url     : https://prove2.me/submissions/4efbb4ed-0f66-477e-b704-77643239196d

import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Definitions.Def_BianchiIX_Statistics_EraBudget
import Theorems.Thm_BianchiIX_eraAmplitude_pos
import Theorems.Thm_BianchiIX_eraAmplitude_series_of_small_beta
import Theorems.Thm_BianchiIX_eraAmplitude_succ
import Theorems.Thm_BianchiIX_eraAmplitude_zero
import Theorems.Thm_BianchiIX_finite_distortion_budget_le
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.List.Induction
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology ENNReal


/-- The root value error drops out of the distortion budget, leaving a tail
of order `B^(4/3)` rather than `B`. -/
theorem solution {B η Cv Ci : ℝ} (hB : 0 < B) (hB1 : B ≤ 1)
    (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2) (hsmall : B ^ η < 1 / 160)
    (hCv : 0 ≤ Cv) (hCi : 0 ≤ Ci) :
    (Summable fun m => Cv * eraAmplitude B m) ∧
      (Summable fun m => Ci * Real.sqrt (eraAmplitude B m)) ∧
      ∀ n, (∑ j ∈ Finset.range n,
        (Ci * Real.sqrt (eraAmplitude B j) + if j = 0 then 0 else 2 * (Cv * eraAmplitude B j))) ≤
          2 * Ci * Real.sqrt B + 4 * Cv * B ^ (4 / 3 : ℝ) := by
  have hηone : η ≤ 1 := by linarith
  have hd : Summable (eraAmplitude B) := by
    simpa only [Nat.add_zero, Real.rpow_one] using
      (eraAmplitude_series_of_small_beta hB hB1 hη hηone hsmall 0).1
  have hds : (∑' m, eraAmplitude B (m + 1)) ≤ 2 * B ^ (4 / 3 : ℝ) := by
    simpa only [Real.rpow_one, eraAmplitude_succ hB.le, eraAmplitude_zero] using
      (eraAmplitude_series_of_small_beta hB hB1 hη hηone hsmall 1).2
  have he : (Summable fun m => Real.sqrt (eraAmplitude B m)) ∧
      (∑' m, Real.sqrt (eraAmplitude B m)) ≤ 2 * Real.sqrt B := by
    simpa only [Nat.add_zero, eraAmplitude_zero, Real.sqrt_eq_rpow] using
      eraAmplitude_series_of_small_beta hB hB1 hη hηhalf hsmall 0
  refine ⟨hd.mul_left Cv, he.1.mul_left Ci, fun n => ?_⟩
  have H := finite_distortion_budget_le (fun m => Cv * eraAmplitude B m)
    (fun m => Ci * Real.sqrt (eraAmplitude B m))
    (fun m => mul_nonneg hCv (eraAmplitude_pos hB m).le)
    (fun _ => mul_nonneg hCi (Real.sqrt_nonneg _)) (hd.mul_left Cv) (he.1.mul_left Ci) n
  rw [tsum_mul_left, tsum_mul_left] at H
  nlinarith [mul_le_mul_of_nonneg_left hds hCv, mul_le_mul_of_nonneg_left he.2 hCi]
