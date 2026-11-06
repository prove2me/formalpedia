-- Prove2me | solution 1 for BianchiIX.normalizedConstraintVolume_normal
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:54:36.4852+00:00
-- url     : https://prove2.me/submissions/7e994981-7e18-49cb-bce3-4884e16a2447

import Definitions.Def_BianchiIX_Dynamics_FlowTransport
import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Theorems.Thm_BianchiIX_basis_det_cons_normal_independent
import Theorems.Thm_BianchiIX_normalizedConstraintDifferential_radial
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

theorem solution {x X : NormalizedState} {v : Fin 4 → NormalizedState}
    (hcon : stateConstraint x = 1) (hX : normalizedConstraintDifferential x X = 1)
    (hv : ∀ i, normalizedConstraintDifferential x (v i) = 0) :
    normalizedConstraintVolume x v =
      normalizedAmbientVolume (Fin.cons X v) / normalizedVolumeWeight x := by
  unfold normalizedConstraintVolume
  congr 1
  exact basis_det_cons_normal_independent (Pi.basisFun ℝ (Fin 5))
    hX (normalizedConstraintDifferential_normal hcon) hv
