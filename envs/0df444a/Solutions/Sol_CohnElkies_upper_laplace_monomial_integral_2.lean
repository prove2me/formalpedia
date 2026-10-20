-- Prove2me | solution 2 for CohnElkies.upper_laplace_monomial_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:27:44.194977+00:00
-- url     : https://prove2.me/submissions/1039d4dc-b9c8-49e1-8aaf-32b6c6c00047

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {η : ℝ} (hη : 0 < η) (k : ℕ) :
    (∫ a : ℝ in Set.Ioi 0,
      a ^ k * Real.exp (-η * a)) =
        (k.factorial : ℝ) / η ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k:ℝ) + 1) (by positivity) hη
  have e1 : ((k:ℝ) + 1 - 1) = (k:ℝ) := by ring
  have h2 : (∫ a : ℝ in Set.Ioi 0, a ^ k * Real.exp (-η * a)) =
      ∫ t : ℝ in Ioi 0, t ^ ((k:ℝ) + 1 - 1) * Real.exp (-(η * t)) := by
    congr 1; funext t; rw [e1, Real.rpow_natCast, neg_mul]
  rw [h2, h, Real.Gamma_nat_eq_factorial, show ((k:ℝ)+1) = ((k+1:ℕ):ℝ) by push_cast; ring,
    Real.rpow_natCast, one_div, inv_pow]
  ring

