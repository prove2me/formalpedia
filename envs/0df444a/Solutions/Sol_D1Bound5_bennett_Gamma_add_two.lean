-- Prove2me | solution 1 for D1Bound5.bennett_Gamma_add_two
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:43:56.402879+00:00
-- url     : https://prove2.me/submissions/4a2c090f-cc07-4cab-bdee-4b7e4a100ee0

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5



theorem _root_.solution (x : ℝ) (hx : 0 < x) :
    Real.Gamma (x + 2) = (x + 1) * x * Real.Gamma x := by
  rw [show x + 2 = (x + 1) + 1 by ring,
    Real.Gamma_add_one (show x + 1 ≠ 0 by linarith), Real.Gamma_add_one hx.ne']
  ring

















end D1Bound5
end
