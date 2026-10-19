-- Prove2me | solution 2 for CohnElkies.lowerRiemannLogPrimitive_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:25:11.962854+00:00
-- url     : https://prove2.me/submissions/de0fbefd-3cc0-4364-8e51-438376ce205d

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
theorem h47_lrlp_hasDerivAt
    {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    HasDerivAt (CohnElkies.lowerRiemannLogPrimitive T)
      (CohnElkies.lowerRiemannLog T x) x := by
  have hb : 0 < |T|/2 := by have := abs_pos.2 hT; positivity
  have hT2 : 0 < T^2 := lt_of_le_of_ne (sq_nonneg T) (Ne.symm (pow_ne_zero 2 hT))
  have hc : 0 < x^2 + T^2/4 := by nlinarith [sq_nonneg x]
  have h1 : HasDerivAt (fun x : ℝ => x^2 + T^2/4) (2*x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const (T^2/4)
  have h2 := h1.log hc.ne'
  have h3 := ((hasDerivAt_id x).div_const 2).mul h2
  have h4 := ((hasDerivAt_id x).div_const (|T|/2)).arctan
  have h5 := (h3.sub (hasDerivAt_id x)).add (h4.const_mul (|T|/2))
  have hbne : |T| ≠ 0 := abs_ne_zero.2 hT
  have hval : 1 / 2 * Real.log (x ^ 2 + T ^ 2 / 4) + id x / 2 * (2 * x / (x ^ 2 + T ^ 2 / 4)) - 1 +
      |T| / 2 * (1 / (1 + (id x / (|T| / 2)) ^ 2) * (1 / (|T| / 2))) = CohnElkies.lowerRiemannLog T x := by
    rw [CohnElkies.lowerRiemannLog, Real.log_sqrt hc.le]
    simp only [id]
    rw [← sq_abs T] at hc ⊢
    have hc' : x ^ 2 + |T| ^ 2 / 4 ≠ 0 := hc.ne'
    field_simp
    ring
  exact h5.congr_deriv hval

theorem solution
    {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    HasDerivAt (lowerRiemannLogPrimitive T)
      (lowerRiemannLog T x) x := by
  exact h47_lrlp_hasDerivAt hT x

