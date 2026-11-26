-- Prove2me | solution 1 for FD1D.TrajectoryBridge.trajectoryLaw_marginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:05:56.345851+00:00
-- url     : https://prove2.me/submissions/b8a12823-e6b0-4475-beba-19223a33e26e

import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Definitions.Def_FD1D_TrajectoryBridge
import Theorems.Thm_FD1D_TrajectoryBridge_trajectoryLaw_marginal_zero
import Theorems.Thm_FD1D_TrajectoryBridge_trajectoryLaw_marginal_succ

set_option autoImplicit true
open FD1D FD1D.TrajectoryBridge
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]
namespace FD1D.TrajectoryBridge
theorem _root_.solution
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ) :
    Measure.map (fun path : ℕ → α => path n) (trajectoryLaw μ₀ κ) =
      iterateLaw κ μ₀ n := by
  induction n with
  | zero =>
      exact trajectoryLaw_marginal_zero μ₀ κ
  | succ n ih =>
      rw [iterateLaw_succ, ← ih]
      exact trajectoryLaw_marginal_succ μ₀ κ n
end FD1D.TrajectoryBridge
