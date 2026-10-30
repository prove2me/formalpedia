-- Prove2me | solution 1 for DerivativeChainContinuation.three_point_radius_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T02:15:16.246217+00:00
-- url     : https://prove2.me/submissions/2e2221eb-17b4-4618-be86-a357481bbb03

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


set_option autoImplicit false
namespace DerivativeChainContinuation

theorem weighted_three_point_identity (a b c : ℂ) (u v w : ℝ) :
    (u+v+w)*(u*Complex.normSq a+v*Complex.normSq b+w*Complex.normSq c) -
      Complex.normSq ((u:ℂ)*a+(v:ℂ)*b+(w:ℂ)*c) =
      u*v*Complex.normSq (a-b)+u*w*Complex.normSq (a-c)+v*w*Complex.normSq (b-c) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring



end DerivativeChainContinuation

open DerivativeChainContinuation in
/-- The circumradius lower bound for every containing disk of a nonobtuse triangle. -/
theorem solution (a b c o : ℂ) (R U V W : ℝ)
    (hR : 0 ≤ R) (ha : ‖a-o‖ ≤ R) (hb : ‖b-o‖ ≤ R) (hc : ‖c-o‖ ≤ R)
    (hU : Complex.normSq (a-b)=U) (hV : Complex.normSq (a-c)=V)
    (hW : Complex.normSq (b-c)=W)
    (hu : 0 ≤ V+W-U) (hv : 0 ≤ U+W-V) (hw : 0 ≤ U+V-W)
    (hs : 0 < 2*(U*V+U*W+V*W)-U^2-V^2-W^2) :
    U*V*W ≤ (2*(U*V+U*W+V*W)-U^2-V^2-W^2)*R^2 := by
  let S := 2*(U*V+U*W+V*W)-U^2-V^2-W^2
  let u := W*(U+V-W)
  let v := V*(U+W-V)
  let w := U*(V+W-U)
  have hU0 : 0 ≤ U := hU ▸ Complex.normSq_nonneg (a-b)
  have hV0 : 0 ≤ V := hV ▸ Complex.normSq_nonneg (a-c)
  have hW0 : 0 ≤ W := hW ▸ Complex.normSq_nonneg (b-c)
  have hu0 : 0 ≤ u := mul_nonneg hW0 hw
  have hv0 : 0 ≤ v := mul_nonneg hV0 hv
  have hw0 : 0 ≤ w := mul_nonneg hU0 hu
  have hsum : u+v+w=S := by dsimp [u,v,w,S]; ring
  have hpair : u*v*U+u*w*V+v*w*W=S*U*V*W := by dsimp [u,v,w,S]; ring
  have hab (z : ℂ) (hz : ‖z-o‖ ≤ R) : Complex.normSq (z-o) ≤ R^2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact (sq_le_sq₀ (norm_nonneg _) hR).mpr hz
  have hbnd : u*Complex.normSq (a-o)+v*Complex.normSq (b-o)+w*Complex.normSq (c-o)
      ≤ S*R^2 := by
    have h1 := mul_le_mul_of_nonneg_left (hab a ha) hu0
    have h2 := mul_le_mul_of_nonneg_left (hab b hb) hv0
    have h3 := mul_le_mul_of_nonneg_left (hab c hc) hw0
    rw [← hsum]
    nlinarith
  have hi := weighted_three_point_identity (a-o) (b-o) (c-o) u v w
  simp only [sub_sub_sub_cancel_right, hU, hV, hW, hsum, hpair] at hi
  have hn := Complex.normSq_nonneg ((u:ℂ)*(a-o)+(v:ℂ)*(b-o)+(w:ℂ)*(c-o))
  have hs' : 0 < S := hs
  have hmul := mul_le_mul_of_nonneg_left hbnd hs'.le
  have hresult : S*(U*V*W) ≤ S*(S*R^2) := by nlinarith
  exact (mul_le_mul_iff_right₀ hs').mp hresult
