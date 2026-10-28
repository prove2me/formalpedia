-- Prove2me | solution 1 for D1Bound5.ordinary_height_scalar_envelope
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:33:41.238974+00:00
-- url     : https://prove2.me/submissions/09873c83-9c8c-4710-8b38-0d020c3fbbec

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

section
namespace D1Bound5



/-- The exact rational-parameter algebra of the ordinary height
envelope. Here x,z,d are base-ten logarithms and p,q are the residual
rate and coefficient-height logarithms. -/
theorem _root_.solution (x z d p q h r u : ℝ)
    (hz : 0 ≤ z) (hq : 0 ≤ q)
    (hp : 2*x+r < p) (hp0 : 0 < 2*x+r)
    (hqh : q < x+h) (hxt : h-r < x)
    (hbound : z*(p-q) < (2*x+u)*p)
    (hd : d < (2/5 : ℝ)-x+2*z) :
    d < 7*x+(4*u+8*h-4*r)+
      (2*u*r+(4*u+8*h-4*r)*(h-r))/(x-(h-r))+(2/5 : ℝ) := by
  have hpPos : 0 < p := hp0.trans hp
  have hxPos : 0 < x-(h-r) := sub_pos.mpr hxt
  have hHpos : 0 < x+h := hq.trans_lt hqh
  have hprod1 := mul_pos (sub_pos.mpr hp) hHpos
  have hprod2 := mul_pos (sub_pos.mpr hqh) hp0
  have hratio : p*(x-(h-r)) < (p-q)*(2*x+r) := by
    nlinarith only [hprod1,hprod2]
  have hlo := mul_le_mul_of_nonneg_left hratio.le hz
  have hhi := mul_lt_mul_of_pos_right hbound hp0
  have hzmul : z*(x-(h-r)) < (2*x+u)*(2*x+r) := by
    by_contra hbad
    have hm := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hbad)) hpPos.le
    nlinarith only [hlo,hhi,hm]
  have hzupper : z < (2*x+u)*(2*x+r)/(x-(h-r)) :=
    (lt_div_iff₀ hxPos).mpr hzmul
  have hid : (2/5 : ℝ)-x+2*((2*x+u)*(2*x+r)/(x-(h-r))) =
      7*x+(4*u+8*h-4*r)+
        (2*u*r+(4*u+8*h-4*r)*(h-r))/(x-(h-r))+(2/5 : ℝ) := by
    field_simp [hxPos.ne'] <;> ring
  rw [← hid]
  linarith only [hd,hzupper]



end D1Bound5
end
