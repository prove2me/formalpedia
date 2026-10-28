-- Prove2me | solution 1 for D1Bound5.unit_pair_cubic_numeric
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:27:19.70829+00:00
-- url     : https://prove2.me/submissions/c10191bd-36dc-4851-b3cf-4bff6e63d723

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section
namespace D1Bound5



/-- Second-order cancellation converts two first-order root estimates
into the cubic unit-pair gap. The lower bound on L is supplied by
integrality, not assumed in the eventual tuple theorem. -/
theorem _root_.solution (C D Z W E F L : ℝ)
    (hC : 9 ≤ C) (hCD : C ≤ D) (hZ0 : 0 < Z) (hW0 : 0 < W)
    (hE0 : 0 ≤ E) (hF0 : 0 ≤ F) (hL : 1 ≤ L)
    (hW : W ≤ C+D) (hZ : C*D ≤ Z^2+1)
    (hE : (15/8 : ℝ)*Z*E < W) (hF : (15/8 : ℝ)*Z*F < W)
    (hcancel : 2*Z*L ≤ E^2+F^2) : C^3/2 < D := by
  have hD : 9 ≤ D := hC.trans hCD
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hD0 : 0 ≤ D := by linarith only [hD]
  have hDpos : 0 < D := by linarith only [hD]
  have hCD81 : 81 ≤ C*D := by
    have hprod := mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hD)
    nlinarith only [hC,hD,hprod]
  have hZlower : (80/81 : ℝ)*C*D ≤ Z^2 := by
    nlinarith only [hCD81,hZ]
  have hEsq : 225*Z^2*E^2 < 64*W^2 := by
    have hp := mul_pos (sub_pos.mpr hE)
      (add_pos_of_pos_of_nonneg hW0 (by positivity : 0 ≤ (15/8 : ℝ)*Z*E))
    nlinarith only [hp]
  have hFsq : 225*Z^2*F^2 < 64*W^2 := by
    have hp := mul_pos (sub_pos.mpr hF)
      (add_pos_of_pos_of_nonneg hW0 (by positivity : 0 ≤ (15/8 : ℝ)*Z*F))
    nlinarith only [hp]
  have hscaled := mul_le_mul_of_nonneg_left hcancel (sq_nonneg Z)
  have hLscaled := mul_nonneg (sub_nonneg.mpr hL) (pow_nonneg hZ0.le 3)
  have hthird : 225*Z^3 < 64*W^2 := by
    nlinarith only [hEsq,hFsq,hscaled,hLscaled]
  have hW2 : W^2 ≤ 4*D^2 := by
    have hWD : W ≤ 2*D := by linarith only [hW,hCD]
    have hp := mul_nonneg (sub_nonneg.mpr hWD)
      (show 0 ≤ 2*D+W by linarith only [hD0,hW0])
    nlinarith only [hp]
  have hthird' : 225*Z^3 < 256*D^2 := by nlinarith only [hthird,hW2]
  have hupper : 225^2*Z^6 < 256^2*D^4 := by
    have hp := mul_pos (sub_pos.mpr hthird')
      (show 0 < 256*D^2+225*Z^3 by positivity)
    nlinarith only [hp]
  have hlower : (80/81 : ℝ)^3*C^3*D^3 ≤ Z^6 := by
    have hp : ((80/81 : ℝ)*C*D)^3 ≤ (Z^2)^3 := by gcongr
    nlinarith only [hp]
  by_contra hbad
  have hprod := mul_nonneg
    (show 0 ≤ C^3-2*D by linarith only [le_of_not_gt hbad])
    (pow_nonneg hD0 3)
  have hD4 : 0 < D^4 := by positivity
  nlinarith only [hupper,hlower,hprod,hD4]

end D1Bound5
end
