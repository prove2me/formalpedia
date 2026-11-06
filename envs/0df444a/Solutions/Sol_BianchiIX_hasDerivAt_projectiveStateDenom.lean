-- Prove2me | solution 1 for BianchiIX.hasDerivAt_projectiveStateDenom
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:24:12.942062+00:00
-- url     : https://prove2.me/submissions/f0ebda3e-f9e0-412e-9660-a9348b446753

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
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
    (hβ : HasDerivAt β (projectiveField (β τ)) τ) :
    HasDerivAt (fun t => projectiveStateDenom (β t))
      (-coupling (β τ 1) (β τ 2) (β τ 3) * projectiveStateDenom (β τ) -
        2 * curvature (β τ 1) (β τ 2) (β τ 3)) τ := by
  have hm := hasDerivAt_pi.mp hβ 0
  have hu := hasDerivAt_pi.mp hβ 1
  have hv := hasDerivAt_pi.mp hβ 2
  have hw := hasDerivAt_pi.mp hβ 3
  convert! (hm.pow 2).const_add 3 |>.add
    (((hu.pow 2).add (hv.pow 2) |>.add (hw.pow 2)).sub
      (((hu.mul hv).add (hv.mul hw) |>.add (hw.mul hu)).const_mul 2)) using 1
  dsimp [projectiveStateDenom, projectiveDenom, projectiveField, curvature,
    phaseVelocity, strongVelocity, activeVelocity, weakVelocity, coupling]
  ring
