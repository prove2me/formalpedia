-- Prove2me | solution 1 for BianchiIX.hasDerivAt_fromProjectiveState
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:32:16.710979+00:00
-- url     : https://prove2.me/submissions/5d3ca5b9-bb20-410e-b118-a9aefdedaf28

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Theorems.Thm_BianchiIX_hasDerivAt_inverseProjectiveScale
import Theorems.Thm_BianchiIX_inverse_projective_field_identity
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
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

noncomputable section
open BianchiIX


theorem solution {β : ℝ → ProjectiveState} {τ : ℝ}
    (hβ : HasDerivAt β (projectiveField (β τ)) τ)
    (hD : projectiveStateDenom (β τ) ≠ 0) :
    HasDerivAt (fun t => fromProjectiveState (β t))
      ((projectiveStateDenom (β τ) / 6) • normalizedField (fromProjectiveState (β τ))) τ := by
  let y := β τ
  let A := 6 / projectiveStateDenom y
  let B := A * coupling (y 1) (y 2) (y 3) + A ^ 2 * curvature (y 1) (y 2) (y 3) / 3
  let W : NormalizedState := ![B,
    (B * y 0 + A * projectiveField y 0) / Real.sqrt 3,
    (B * y 1 + A * projectiveField y 1) / Real.sqrt 3,
    (B * y 2 + A * projectiveField y 2) / Real.sqrt 3,
    (B * y 3 + A * projectiveField y 3) / Real.sqrt 3]
  have hA := hasDerivAt_inverseProjectiveScale hβ hD
  have hW : HasDerivAt (fun t => fromProjectiveState (β t)) W τ := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hA.sub_const 1
    · exact (hA.mul (hasDerivAt_pi.mp hβ 0)).div_const (Real.sqrt 3)
    · exact (hA.mul (hasDerivAt_pi.mp hβ 1)).div_const (Real.sqrt 3)
    · exact (hA.mul (hasDerivAt_pi.mp hβ 2)).div_const (Real.sqrt 3)
    · exact (hA.mul (hasDerivAt_pi.mp hβ 3)).div_const (Real.sqrt 3)
  have hAD : A * projectiveDenom (y 0) (y 1) (y 2) (y 3) = 6 := by
    change 6 / projectiveStateDenom y * projectiveStateDenom y = 6
    exact div_mul_cancel₀ _ hD
  have hfield : A • W = normalizedField (fromProjectiveState y) :=
    inverse_projective_field_identity A (y 0) (y 1) (y 2) (y 3) hAD
  have hinv : projectiveStateDenom y / 6 * A = 1 := by
    dsimp [A]
    field_simp [show projectiveStateDenom y ≠ 0 from hD]
  change HasDerivAt _ ((projectiveStateDenom y / 6) • normalizedField (fromProjectiveState y)) τ
  rw [← hfield, smul_smul, hinv, one_smul]
  exact hW
