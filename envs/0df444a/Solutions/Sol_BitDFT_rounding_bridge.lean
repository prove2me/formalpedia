-- Prove2me | solution 1 for BitDFT.rounding_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:02:44.727902+00:00
-- url     : https://prove2.me/submissions/01542dd3-5433-4ea5-b6b7-76abf3141644

import Definitions.Def_BitDFT_Numerics
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
noncomputable section
open BitDFT

theorem solution (p : ℕ) (z : ℂ) :
    value p (roundPair p z) = IntMul.HvdH.rho p z := by
  simp only [value, roundPair, IntMul.HvdH.rho, IntMul.HvdH.rho0C, div_eq_mul_inv]
  ring

#print axioms solution
