-- Prove2me | solution 1 for BianchiIX.InverseBranchTree.BranchEstimates.restricted_loss_of_amplitude_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:16:25.21348+00:00
-- url     : https://prove2.me/submissions/d8b7e89b-1daf-460f-b6b1-adb11a7537f1

import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Definitions.Def_BianchiIX_Statistics_EraBudget
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_restricted_root_loss_le
import Theorems.Thm_BianchiIX_era_distortion_budget
import Theorems.Thm_BianchiIX_era_stopping_budget
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
open BianchiIX.InverseBranchTree
open BianchiIX.InverseBranchTree.BranchEstimates


theorem solution {T : InverseBranchTree} {B η Cv Ci : ℝ}
    (E : T.BranchEstimates (fun m => Cv * eraAmplitude B m)
      (fun m => Ci * Real.sqrt (eraAmplitude B m)))
    (hB : 0 < B) (hB1 : B ≤ 1) (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hsmall : B ^ η < 1 / 160) (hCv : 0 ≤ Cv) (hCi : 0 ≤ Ci)
    (hL : 2 * Ci * Real.sqrt B + 4 * Cv * B ^ (4 / 3 : ℝ) ≤ Real.log 2)
    (hsize : ∀ w, volume (T.stoppedDomain w) ≤ ENNReal.ofReal (10 * eraAmplitude B w.length ^ η))
    (I : Set ℝ) :
    volume ((I ∩ T.root) \ (I ∩ T.survivors)) ≤ min (volume I) (ENNReal.ofReal (80 * B ^ η)) := by
  have hb := (era_distortion_budget hB hB1 hη hηhalf hsmall hCv hCi).2.2
  have H := E.restricted_root_loss_le I (fun m => ENNReal.ofReal (10 * eraAmplitude B m ^ η))
    (fun n => (hb n).trans hL) hsize
  refine H.trans (min_le_min_left _ ?_)
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * ENNReal.ofReal 2 * (∑' m, ENNReal.ofReal (10 * eraAmplitude B m ^ η)) ≤
        2 * ENNReal.ofReal 2 * ENNReal.ofReal (20 * B ^ η) :=
      mul_le_mul le_rfl (era_stopping_budget hB hB1 hη hsmall) (by positivity) (by positivity)
    _ = ENNReal.ofReal (80 * B ^ η) := by
      rw [show (80 : ℝ) * B ^ η = 4 * (20 * B ^ η) by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
