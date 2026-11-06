-- Prove2me | solution 1 for BianchiIX.normalizedConstraintVolume_flow
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:03:09.329595+00:00
-- url     : https://prove2.me/submissions/eaad2ff2-2b7d-408f-a9e8-dd74dd320f7b

import Definitions.Def_BianchiIX_Dynamics_FlowTransport
import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Theorems.Thm_BianchiIX_NormalizedSolution_physical
import Theorems.Thm_BianchiIX_normalizedConstraintDifferential_flow
import Theorems.Thm_BianchiIX_normalizedConstraintDifferential_radial
import Theorems.Thm_BianchiIX_normalizedConstraintVolume_normal
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
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedConstraintDifferential_normal {x : NormalizedState} (hx : stateConstraint x = 1) :
    normalizedConstraintDifferential x ((1 / 2 : ℝ) • x) = 1 := by
  rw [map_smul, normalizedConstraintDifferential_radial, hx]
  norm_num

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology

private theorem BianchiIX.normalizedVolumeWeight_pos {x : NormalizedState} (hx : positiveWalls x) :
    0 < normalizedVolumeWeight x := by
  have hh : 0 ≤ wallAmplitude (x 2) (x 3) (x 4) :=
    Real.rpow_nonneg (mul_pos (mul_pos hx.1 hx.2.1) hx.2.2).le _
  exact mul_pos (mul_pos (mul_pos hx.1 hx.2.1) hx.2.2) (by linarith)

end
end

theorem solution {x : NormalizedState} {t₀ t : ℝ}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (ht : t ∈ normalizedMaxDomain x t₀) (v : Fin 4 → NormalizedState)
    (hv : ∀ i, normalizedConstraintDifferential x (v i) = 0) :
    normalizedConstraintVolume (normalizedMaxCurve x t₀ t)
        (fun i => normalizedFlowDifferential x t₀ t (v i)) =
      normalizedVolumeJacobian x t₀ t * normalizedConstraintVolume x v := by
  let z := normalizedMaxCurve x t₀ t
  let P := normalizedFlowDifferential x t₀ t
  have hp : positiveWalls z ∧ stateConstraint z = 1 :=
    (maximalNormalizedSolution x t₀).physical hpos hcon ht
  have hcov (u : NormalizedState) : normalizedConstraintDifferential z (P u) =
      normalizedConstraintDifferential x u :=
    congrArg (fun L : NormalizedState →L[ℝ] ℝ => L u) (normalizedConstraintDifferential_flow ht)
  have hnormal : normalizedConstraintDifferential z (P ((1 / 2 : ℝ) • x)) = 1 := by
    rw [hcov, normalizedConstraintDifferential_normal hcon]
  have hdet : normalizedAmbientVolume (Fin.cons (P ((1 / 2 : ℝ) • x)) (fun i => P (v i))) =
      P.det * normalizedAmbientVolume (Fin.cons ((1 / 2 : ℝ) • x) v) := by
    have H := (Pi.basisFun ℝ (Fin 5)).det_comp P.toLinearMap (Fin.cons ((1 / 2 : ℝ) • x) v)
    rw [Fin.comp_cons] at H
    exact H
  change normalizedConstraintVolume z (fun i => P (v i)) = _
  rw [normalizedConstraintVolume_normal hp.2 hnormal (fun i => (hcov (v i)).trans (hv i))]
  rw [hdet]
  have hw := ne_of_gt (normalizedVolumeWeight_pos hpos)
  unfold normalizedVolumeJacobian normalizedConstraintVolume
  dsimp [P, z]
  field_simp [hw]
