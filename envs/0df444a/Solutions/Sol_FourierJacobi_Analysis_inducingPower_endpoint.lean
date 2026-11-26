-- Prove2me | solution 1 for FourierJacobi.Analysis.inducingPower_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:38.62633+00:00
-- url     : https://prove2.me/submissions/78639d69-2eac-45bd-a988-52c481911baa

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
    inducingPower q (1 / 2) = q⁻¹ := by
  unfold inducingPower
  rw [show (-2 * Real.log q) * (1 / 2) = -Real.log q by ring,
    Real.exp_neg, Real.exp_log hq]
end FourierJacobi.Analysis
