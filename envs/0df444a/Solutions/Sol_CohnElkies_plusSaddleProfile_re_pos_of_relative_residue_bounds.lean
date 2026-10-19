-- Prove2me | solution 1 for CohnElkies.plusSaddleProfile_re_pos_of_relative_residue_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/ee7acb49-4eed-4bac-a49b-84192ecfd171

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusSaddleProfile_div_origin_eq_small_radius_residue_series

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ r : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r)
    (N : ℕ)
    (hfinite :
      Real.exp (saddleSmallRadiusVariable ε r) *
        |(∑ n ∈ Finset.range (N + 1),
            (-saddleSmallRadiusVariable ε r) ^ n /
              (n.factorial : ℝ) *
                plusSaddleSmallRadiusCoefficient ε ℓ n) -
          Real.exp (-(saddleSmallRadiusVariable ε r))| <
        (1 / 2 : ℝ))
    (hremainder :
      Real.exp (saddleSmallRadiusVariable ε r) *
        ‖plusSaddleTaylorRemainder ε ℓ N r /
          (saddleOriginValue ε ℓ : ℂ)‖ <
        (1 / 2 : ℝ)) :
    0 < (plusSaddleProfile ε ℓ r).re := by
  let y : ℝ := saddleSmallRadiusVariable ε r
  let S : ℝ :=
    ∑ n ∈ Finset.range (N + 1),
      (-y) ^ n / (n.factorial : ℝ) *
        plusSaddleSmallRadiusCoefficient ε ℓ n
  let Q : ℂ :=
    plusSaddleTaylorRemainder ε ℓ N r /
      (saddleOriginValue ε ℓ : ℂ)
  have hO : 0 < saddleOriginValue ε ℓ :=
    saddleOriginValue_pos hε ℓ
  have hnormal :
      (plusSaddleProfile ε ℓ r).re /
          saddleOriginValue ε ℓ = S + Q.re := by
    have h := congrArg Complex.re
      (plusSaddleProfile_div_origin_eq_small_radius_residue_series
        hε hℓ horder hr N)
    simpa [S, Q, y, Complex.div_ofReal_re,
      ← Complex.ofReal_neg, ← Complex.ofReal_pow] using! h
  have hexp : 0 < Real.exp y := Real.exp_pos y
  have hone : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add]
    simp
  have hfinite' :
      Real.exp y * |S - Real.exp (-y)| < (1 / 2 : ℝ) := by
    simpa [S, y] using! hfinite
  have hremainder' :
      Real.exp y * ‖Q‖ < (1 / 2 : ℝ) := by
    simpa [Q, y] using! hremainder
  have hSabs :
      -|S - Real.exp (-y)| ≤ S - Real.exp (-y) :=
    neg_abs_le _
  have hSlower :
      (1 / 2 : ℝ) < Real.exp y * S := by
    have hscaled := mul_le_mul_of_nonneg_left
      hSabs hexp.le
    nlinarith
  have hQabs := Complex.abs_re_le_norm Q
  have hQneg : -‖Q‖ ≤ Q.re := by
    nlinarith [neg_abs_le Q.re]
  have hQlower :
      -(1 / 2 : ℝ) < Real.exp y * Q.re := by
    have hscaled := mul_le_mul_of_nonneg_left
      hQneg hexp.le
    nlinarith
  have hsum : 0 < S + Q.re := by
    have hscaled : 0 < Real.exp y * (S + Q.re) := by
      nlinarith
    exact (mul_pos_iff_of_pos_left hexp).mp hscaled
  exact (div_pos_iff_of_pos_right hO).mp
    (hnormal.symm ▸ hsum)
end CohnElkies
