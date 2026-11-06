-- Prove2me | solution 1 for BianchiIX.normalizedVolumeJacobian_eq_exp_integral
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:13:19.51826+00:00
-- url     : https://prove2.me/submissions/1ea263b8-fd1e-4c66-9d65-a2c5b4a10f5a

import Definitions.Def_BianchiIX_Dynamics_CorrectedVolume
import Theorems.Thm_BianchiIX_NormalizedSolution_physical
import Theorems.Thm_BianchiIX_continuousAt_normalizedCorrectedDivergence
import Theorems.Thm_BianchiIX_hasDerivAt_normalizedVolumeJacobian
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi

noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.homogeneous_solution_eq_exp_integral {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {f a : ℝ → ℝ} (ha : ContinuousOn a I)
    (hf : ∀ t ∈ I, HasDerivAt f (a t * f t) t) {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    f t = f t₀ * Real.exp (∫ u in t₀..t, a u) := by
  let P : ℝ → ℝ := fun v => ∫ u in t₀..v, a u
  have hP (v : ℝ) (hv : v ∈ I) : HasDerivAt P (a v) v :=
    intervalIntegral.integral_hasDerivAt_right
      (ha.mono (hI.ordConnected.uIcc_subset ht₀ hv)).intervalIntegrable
      (ContinuousOn.stronglyMeasurableAtFilter hopen ha v hv)
      (ha.continuousAt (hopen.mem_nhds hv))
  have hF (v : ℝ) (hv : v ∈ I) :
      HasDerivAt (fun u => f u * Real.exp (-P u)) 0 v := by
    convert! (hf v hv).mul (hP v hv).neg.exp using 1
    ring
  have H := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v hv => (hF v hv).hasDerivWithinAt) (C := 0) (fun _ _ => by simp) ht₀ ht
  have heq : f t * Real.exp (-P t) = f t₀ := by
    simpa [P, sub_eq_zero] using H
  calc
    f t = (f t * Real.exp (-P t)) * Real.exp (P t) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = f t₀ * Real.exp (P t) := by rw [heq]

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.normalizedFlowDifferential_initial (x : NormalizedState) (t₀ : ℝ) :
    normalizedFlowDifferential x t₀ t₀ = ContinuousLinearMap.id ℝ NormalizedState := by
  simp [normalizedFlowDifferential, normalizedMaxCurve_initial]

end
end

private theorem BianchiIX.normalizedVolumeWeight_pos {x : NormalizedState} (hx : positiveWalls x) :
    0 < normalizedVolumeWeight x := by
  have hh : 0 ≤ wallAmplitude (x 2) (x 3) (x 4) :=
    Real.rpow_nonneg (mul_pos (mul_pos hx.1 hx.2.1) hx.2.2).le _
  exact mul_pos (mul_pos (mul_pos hx.1 hx.2.1) hx.2.2) (by linarith)

private theorem BianchiIX.normalizedVolumeJacobian_initial {x : NormalizedState} (hpos : positiveWalls x) (t₀ : ℝ) :
    normalizedVolumeJacobian x t₀ t₀ = 1 := by
  simp [normalizedVolumeJacobian, normalizedFlowDifferential_initial, ContinuousLinearMap.det,
    normalizedMaxCurve_initial, ne_of_gt (normalizedVolumeWeight_pos hpos)]

theorem solution {x : NormalizedState} {t₀ t : ℝ}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (ht : t ∈ normalizedMaxDomain x t₀) :
    normalizedVolumeJacobian x t₀ t =
      Real.exp (∫ u in t₀..t, normalizedCorrectedDivergence (normalizedMaxCurve x t₀ u)) := by
  have hc : ContinuousOn (fun u => normalizedCorrectedDivergence (normalizedMaxCurve x t₀ u))
      (normalizedMaxDomain x t₀) := by
    intro u hu
    exact ((continuousAt_normalizedCorrectedDivergence
      ((maximalNormalizedSolution x t₀).physical hpos hcon hu).1).comp
        (hasDerivAt_normalizedMaxCurve hu).continuousAt).continuousWithinAt
  have H := homogeneous_solution_eq_exp_integral (convex_normalizedMaxDomain x t₀)
    (isOpen_normalizedMaxDomain x t₀) hc
    (fun _ hu => hasDerivAt_normalizedVolumeJacobian hpos hcon hu)
    (initial_mem_normalizedMaxDomain x t₀) ht
  simpa only [normalizedVolumeJacobian_initial hpos, one_mul] using H
