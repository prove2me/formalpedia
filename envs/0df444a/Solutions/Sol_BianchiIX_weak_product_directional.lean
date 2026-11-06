-- Prove2me | solution 1 for BianchiIX.weak_product_directional
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:05:03.642144+00:00
-- url     : https://prove2.me/submissions/d840faa5-c7d2-441b-bf60-3bb32c6e6df6

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
    activeVelocity m u v w * w + v * weakVelocity m u v w =
      -2 * (1 + coupling u v w) * (v * w) := by
  unfold activeVelocity weakVelocity
  ring
