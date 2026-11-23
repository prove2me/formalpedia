-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Rec.pow_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:11.428188+00:00
-- url     : https://prove2.me/submissions/ea74bdc4-4675-4bfb-8770-c33682e6fb26

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SharpRecursion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_quart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Rec
open Finset Real
namespace Formalism.FourierDecayAlt.P.Rec
theorem _root_.solution (r : ℕ) (a ε : ℝ) (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (hx : ((r:ℝ) + 1) * (ε + a) ≤ 1) :
    ((1 + ε + 2 * a) ^ (r+1)) ^ 2 ≤ 1 + 80 * ((r:ℝ) + 1) * (ε + a) := by
  have hx0 : 0 ≤ ((r:ℝ) + 1) * (ε + a) := by positivity
  have h1 : 1 + ε + 2 * a ≤ Real.exp (2 * (ε + a)) := by
    have := Real.add_one_le_exp (2 * (ε + a)); linarith
  have h2 : (1 + ε + 2 * a) ^ (r+1) ≤ Real.exp (((r+1 : ℕ) : ℝ) * (2 * (ε + a))) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (by linarith) h1 _
  have h3 : Real.exp (((r+1 : ℕ) : ℝ) * (2 * (ε + a))) =
      Real.exp (((r:ℝ) + 1) * (ε + a)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h3] at h2
  have hE := Real.abs_exp_sub_one_le (x := ((r:ℝ) + 1) * (ε + a))
    (by rw [abs_of_nonneg hx0]; exact hx)
  rw [abs_of_nonneg hx0] at hE
  have hE' : Real.exp (((r:ℝ) + 1) * (ε + a)) ≤ 1 + 2 * (((r:ℝ) + 1) * (ε + a)) := by
    linarith [le_abs_self (Real.exp (((r:ℝ) + 1) * (ε + a)) - 1)]
  have hEn : 0 ≤ Real.exp (((r:ℝ) + 1) * (ε + a)) := (Real.exp_pos _).le
  have hρn : 0 ≤ (1 + ε + 2 * a) ^ (r+1) := pow_nonneg (by linarith) _
  have s1 := pow_le_pow_left₀ hρn h2 2
  have s2 := pow_le_pow_left₀ hEn hE' 4
  have s3 := quart (((r:ℝ) + 1) * (ε + a)) hx0 hx
  have e4 : (Real.exp (((r:ℝ) + 1) * (ε + a)) ^ 2) ^ 2 =
      Real.exp (((r:ℝ) + 1) * (ε + a)) ^ 4 := by ring
  have e5 : 80 * ((r:ℝ) + 1) * (ε + a) = 80 * (((r:ℝ) + 1) * (ε + a)) := by ring
  rw [e5]
  linarith
end Formalism.FourierDecayAlt.P.Rec
