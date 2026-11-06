-- Prove2me | solution 1 for BianchiIX.constraint_of_inverse_projective
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:27:15.435208+00:00
-- url     : https://prove2.me/submissions/751e3718-3b9b-4033-b710-7caf46051730

import Definitions.Def_BianchiIX_Algebra_Coordinates
import Theorems.Thm_BianchiIX_constraint_of_projective
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

open BianchiIX
noncomputable section


theorem solution
    {m u v w : ℝ} (hD : projectiveDenom m u v w ≠ 0) :
    let A := 6 / projectiveDenom m u v w
    constraint (A - 1) (A * m / Real.sqrt 3) (A * u / Real.sqrt 3)
      (A * v / Real.sqrt 3) (A * w / Real.sqrt 3) = 1 := by
  apply constraint_of_projective
  field_simp
