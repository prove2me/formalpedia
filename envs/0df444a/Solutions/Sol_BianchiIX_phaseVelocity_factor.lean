-- Prove2me | solution 1 for BianchiIX.phaseVelocity_factor
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:05:01.457402+00:00
-- url     : https://prove2.me/submissions/ef5f18bc-9307-4bdf-a30f-521f0233a184

import Definitions.Def_BianchiIX_Algebra_Projective
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BianchiIX
noncomputable section


theorem solution (m u v w : ℝ) :
    phaseVelocity m u v w = -(v + w - u) * (v - w + m * u) := by
  unfold phaseVelocity coupling
  ring
