-- Prove2me | solution 1 for CourierDispatch.Exogenous.wait_difference_eq
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T09:30:22.225987+00:00
-- url     : https://prove2.me/submissions/692ad323-7ba8-4c9b-a67d-835177e652c6

import Mathlib
import Definitions.Def_CourierDispatch_Exogenous_Setting

open CourierDispatch.Exogenous

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Mingliu Chen and Ming Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063.
theorem solution (CB r lam : ℝ) (hr : 0 < r) (hlam : 0 < lam) (hstab : lam*r < TD) :
    WD lam (muD r) CD-WB r lam (muB r) CB = fA CB (lam*r)/lam := by
  have hp := Real.pi_pos
  have hdb : 32+15*Real.pi ≠ 0 := by positivity
  have hmuD : muD r = TD/r := by unfold muD TD; ring
  have hmuB : muB r = TB/(2*r) := by
    unfold muB TB
    field_simp
    ring
  have hTB : TD < TB := by
    unfold TD TB
    apply (lt_div_iff₀ (by positivity : 0 < 2*(32+15*Real.pi))).2
    linarith [Real.pi_gt_three]
  have hTD : TD ≠ 0 := by norm_num [TD]
  have hTB0 : TB ≠ 0 := by
    have hTDpos : 0 < TD := by norm_num [TD]
    exact (hTDpos.trans hTB).ne'
  have hd : TD-r*lam ≠ 0 := by nlinarith only [hstab]
  have hb : TB-r*lam ≠ 0 := by nlinarith only [hstab,hTB]
  rw [hmuD,hmuB]
  unfold WD WB fA
  field_simp [hr.ne',hlam.ne',hTD,hTB0,hd,hb]
  ring

#print axioms solution
