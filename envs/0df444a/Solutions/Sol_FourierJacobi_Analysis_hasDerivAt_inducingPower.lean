-- Prove2me | solution 1 for FourierJacobi.Analysis.hasDerivAt_inducingPower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:41.81292+00:00
-- url     : https://prove2.me/submissions/8dcd94bf-1eae-476d-b0cb-edb8f3699382

import Definitions.Def_FourierJacobi_Algebra_Intertwiner
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Definitions.Def_FourierJacobi_Analysis_IntertwinerDerivative

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 0 < q) :
    HasDerivAt (inducingPower q) (-2 * Real.log q / q) (1 / 2) := by
  have h := ((hasDerivAt_id (1 / 2 : ℝ)).const_mul (-2 * Real.log q)).exp
  convert h using 1
  · rfl
  · dsimp
    rw [show (-2 * Real.log q) * (1 / 2) = -Real.log q by ring,
      Real.exp_neg, Real.exp_log hq]
    ring
end FourierJacobi.Analysis
