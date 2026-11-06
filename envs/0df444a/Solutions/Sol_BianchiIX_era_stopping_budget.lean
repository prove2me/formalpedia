-- Prove2me | solution 1 for BianchiIX.era_stopping_budget
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:15:04.823219+00:00
-- url     : https://prove2.me/submissions/5efde66d-1feb-4799-a2c7-8700908e2423

import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Definitions.Def_BianchiIX_Statistics_EraBudget
import Theorems.Thm_BianchiIX_eraAmplitude_pos
import Theorems.Thm_BianchiIX_eraAmplitude_series_of_small_beta
import Theorems.Thm_BianchiIX_eraAmplitude_zero
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


theorem solution {B η : ℝ} (hB : 0 < B) (hB1 : B ≤ 1)
    (hη : 0 ≤ η) (hsmall : B ^ η < 1 / 160) :
    (∑' m, ENNReal.ofReal (10 * eraAmplitude B m ^ η)) ≤ ENNReal.ofReal (20 * B ^ η) := by
  have H : (Summable fun m => eraAmplitude B m ^ η) ∧
      (∑' m, eraAmplitude B m ^ η) ≤ 2 * B ^ η := by
    simpa only [Nat.add_zero, eraAmplitude_zero] using
      eraAmplitude_series_of_small_beta hB hB1 hη le_rfl hsmall 0
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun m => mul_nonneg (by norm_num) (Real.rpow_nonneg (eraAmplitude_pos hB m).le η))
    (H.1.mul_left 10)]
  apply ENNReal.ofReal_le_ofReal
  rw [tsum_mul_left]
  linarith [H.2]
