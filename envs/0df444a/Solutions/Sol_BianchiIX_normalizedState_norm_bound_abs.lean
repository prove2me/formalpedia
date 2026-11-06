-- Prove2me | solution 1 for BianchiIX.normalizedState_norm_bound_abs
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:55:45.500956+00:00
-- url     : https://prove2.me/submissions/c3a1d3ed-aff8-4a61-ac1d-6e4c38129d57

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
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

noncomputable section
open BianchiIX
open Set MeasureTheory


/-- The constraint controls the shear using absolute wall bounds; positivity is unnecessary. -/
theorem solution {x : NormalizedState} {M : ℝ}
    (hcon : stateConstraint x = 1) (hwall : ∀ i : Fin 3, |wallValue i x| ≤ M) :
    ‖x‖ ≤ 1 + 3 * M := by
  have h₂ : |x 2| ≤ M := hwall 0
  have h₃ : |x 3| ≤ M := hwall 1
  have h₄ : |x 4| ≤ M := hwall 2
  have hM : 0 ≤ M := (abs_nonneg _).trans h₂
  have hsum : |x 2 + x 3 + x 4| ≤ 3 * M := by
    calc
      _ ≤ |x 2 + x 3| + |x 4| := abs_add_le _ _
      _ ≤ |x 2| + |x 3| + |x 4| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 3 * M := by linarith
  have hsum2 : (x 2 + x 3 + x 4) ^ 2 ≤ (3 * M) ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_nonneg (by positivity : 0 ≤ 3 * M)] using hsum)
  have hconstraint : x 0 ^ 2 + x 1 ^ 2 + curvature (x 2) (x 3) (x 4) = 1 := hcon
  unfold curvature at hconstraint
  have hS : x 0 ^ 2 + x 1 ^ 2 ≤ 1 + 9 * M ^ 2 := by
    nlinarith [sq_nonneg (x 2), sq_nonneg (x 3), sq_nonneg (x 4)]
  have hR : 0 ≤ 1 + 3 * M := by positivity
  have hp : |x 0| ≤ 1 + 3 * M := by
    apply (sq_le_sq₀ (abs_nonneg _) hR).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (x 1)]
  have hs : |x 1| ≤ 1 + 3 * M := by
    apply (sq_le_sq₀ (abs_nonneg _) hR).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (x 0)]
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  fin_cases i
  · exact hp
  · exact hs
  · change |x 2| ≤ 1 + 3 * M
    linarith
  · change |x 3| ≤ 1 + 3 * M
    linarith
  · change |x 4| ≤ 1 + 3 * M
    linarith
