-- Prove2me | solution 1 for AvramDividend.Classical.derivZeroPlus_of_local_volterra_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:22:42.639237+00:00
-- url     : https://prove2.me/submissions/f836ef80-b822-4869-a9a9-18b251b522ac

import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_eq_coe_of_right_tendsto
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.LiminfLimsup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Filter Set
open scoped NNReal ENNReal

theorem solution
    (W G : ℝ → ℝ) (d a : ℝ)
    (hW0 : W 0 = 1 / d)
    (hWcont : ContinuousWithinAt W (Ioi (0 : ℝ)) 0)
    (hG : Tendsto G (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    (hDer : ∀ x : ℝ, 0 < x → deriv W x = a * W x - G x / d) :
    derivZeroPlus W = ((a / d : ℝ) : EReal) := by
  have hWlim : Tendsto W (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (1 / d)) := by
    simpa only [hW0] using hWcont.tendsto
  have hmul : Tendsto (fun x : ℝ => a * W x)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (a * (1 / d))) :=
    tendsto_const_nhds.mul hWlim
  have hdiv : Tendsto (fun x : ℝ => G x / d)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 / d)) :=
    hG.div_const d
  have hlim : Tendsto (fun x : ℝ => a * W x - G x / d)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (a / d)) := by
    convert hmul.sub hdiv using 1 <;> simp [div_eq_mul_inv]
  have heq : (fun x : ℝ => deriv W x) =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun x : ℝ => a * W x - G x / d) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hDer x hx
  exact derivZeroPlus_eq_coe_of_right_tendsto W (a / d)
    (hlim.congr' heq.symm)
