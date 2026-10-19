-- Prove2me | solution 2 for CohnElkies.integrable_exp_neg_mul_abs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:16:59.917027+00:00
-- url     : https://prove2.me/submissions/8341c5fe-4f1a-446d-98c8-7870e0831180

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology


theorem solution {a : ℝ} (ha : 0 < a) :
    Integrable (fun T : ℝ => Real.exp (-a * |T|)) := by
  have h1 : IntegrableOn (fun T : ℝ => Real.exp (-a * |T|)) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic ha 0).congr_fun (fun T hT => ?_) measurableSet_Iic
    simp only
    rw [abs_of_nonpos (show T ≤ 0 from hT)]; ring_nf
  have h2 : IntegrableOn (fun T : ℝ => Real.exp (-a * |T|)) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (by linarith : -a < 0) 0).congr_fun (fun T hT => ?_) measurableSet_Ioi
    simp only
    rw [abs_of_pos (show (0:ℝ) < T from hT)]
  have := h1.union h2
  rwa [Iic_union_Ioi, integrableOn_univ] at this

