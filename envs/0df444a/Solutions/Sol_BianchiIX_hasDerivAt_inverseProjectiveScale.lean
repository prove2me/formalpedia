-- Prove2me | solution 1 for BianchiIX.hasDerivAt_inverseProjectiveScale
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:28:33.506204+00:00
-- url     : https://prove2.me/submissions/553950e1-dfd2-4f12-ad48-f0e938f0ca22

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveStateDenom
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
    HasDerivAt (fun t => 6 / projectiveStateDenom (β t))
      ((6 / projectiveStateDenom (β τ)) * coupling (β τ 1) (β τ 2) (β τ 3) +
        (6 / projectiveStateDenom (β τ)) ^ 2 * curvature (β τ 1) (β τ 2) (β τ 3) / 3) τ := by
  convert! (hasDerivAt_const τ (6 : ℝ)).div (hasDerivAt_projectiveStateDenom hβ) hD using 1
  field_simp
  ring
