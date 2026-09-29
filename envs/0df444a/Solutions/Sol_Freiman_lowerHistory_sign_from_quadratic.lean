-- Prove2me | solution 1 for Freiman.lowerHistory_sign_from_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T10:50:56.057928+00:00
-- url     : https://prove2.me/submissions/78b0eff3-b01a-4b3a-aba1-9e597923c0bc

import Definitions.Def_Freiman_lowerHistoryAlgebra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ring

open Freiman
set_option maxHeartbeats 0

theorem solution (hq : ∀ a b : ℚ,
    (lowerHistoryQuadSign a b 3 = 0 ↔ (a:ℝ)+b*Real.sqrt 3=0) ∧
    (0<lowerHistoryQuadSign a b 3 ↔ 0<(a:ℝ)+b*Real.sqrt 3)) (z : CertField) :
    (lowerHistorySign z = 0 ↔ certFieldVal z = 0) ∧
    (0 < lowerHistorySign z ↔ 0 < certFieldVal z) := by
  let x : ℝ := z.a + z.b * Real.sqrt 3
  let y : ℝ := z.c + z.d * Real.sqrt 3
  let u : ℚ := z.a^2 + 3*z.b^2 - 7*z.c^2 - 21*z.d^2
  let v : ℚ := 2*z.a*z.b - 14*z.c*z.d
  have hx := hq z.a z.b
  have hy := hq z.c z.d
  have hn := hq u v
  change (_ ↔ x=0) ∧ (_ ↔ 0<x) at hx
  change (_ ↔ y=0) ∧ (_ ↔ 0<y) at hy
  have hs : 0 < Real.sqrt 7 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 7)^2 = 7 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have h21 : Real.sqrt 21 = Real.sqrt 3 * Real.sqrt 7 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  have hv : certFieldVal z = x+y*Real.sqrt 7 := by
    simp only [certFieldVal, x, y, h21]
    ring
  have hnorm : (u:ℝ)+(v:ℝ)*Real.sqrt 3 = x^2-7*y^2 := by
    dsimp [u,v,x,y]
    push_cast
    ring_nf
    rw [h3]
    ring
  rw [hnorm] at hn
  have he : (x+y*Real.sqrt 7)*(x-y*Real.sqrt 7) = x^2-7*y^2 := by
    calc
      _ = x^2-y^2*(Real.sqrt 7)^2 := by ring
      _ = _ := by rw [hs2]; ring
  rw [hv]
  simp only [lowerHistorySign]
  split_ifs with xz yz xp yp yn
  · have hx0 := hx.1.mp xz
    simp only [hx0, zero_add]
    exact ⟨by rw [hy.1, mul_eq_zero, or_iff_left hs.ne'],
      by rw [hy.2, mul_pos_iff_of_pos_right hs]⟩
  · have hy0 := hy.1.mp yz
    simpa [hy0] using hx
  · have hxr := hx.2.mp xp
    have hyr := hy.2.mp yp
    have hpos : 0 < x+y*Real.sqrt 7 := by positivity
    simp [ne_of_gt hpos,hpos]
  · have hxr := hx.2.mp xp
    have hyr : y < 0 := lt_of_le_of_ne (le_of_not_gt (fun h => yp (hy.2.mpr h))) (mt hy.1.mpr yz)
    have hc : 0 < x-y*Real.sqrt 7 := by nlinarith [mul_neg_of_neg_of_pos hyr hs]
    constructor
    · rw [hn.1, ← he, mul_eq_zero, or_iff_left hc.ne']
    · rw [hn.2, ← he, mul_pos_iff_of_pos_right hc]
  · have hxr : x < 0 := lt_of_le_of_ne (le_of_not_gt (fun h => xp (hx.2.mpr h))) (mt hx.1.mpr xz)
    have hyr : y < 0 := by
      have hp : ¬ 0 < y := fun h => (not_lt_of_ge yn.le) (hy.2.mpr h)
      exact lt_of_le_of_ne (le_of_not_gt hp) (mt hy.1.mpr yz)
    have hneg : x+y*Real.sqrt 7 < 0 := by nlinarith [mul_neg_of_neg_of_pos hyr hs]
    simp [ne_of_lt hneg,not_lt_of_ge hneg.le]
  · have hxr : x < 0 := lt_of_le_of_ne (le_of_not_gt (fun h => xp (hx.2.mpr h))) (mt hx.1.mpr xz)
    have hyr : 0 < y := hy.2.mp (lt_of_le_of_ne (le_of_not_gt yn) (Ne.symm yz))
    have hc : x-y*Real.sqrt 7 < 0 := by nlinarith [mul_pos hyr hs]
    have hnn : lowerHistoryQuadSign u v 3 < 0 ↔ x^2-7*y^2 < 0 := by
      constructor
      · intro h
        have h0 : x^2-7*y^2 ≠ 0 := fun hh => (ne_of_lt h) (hn.1.mpr hh)
        have hp : ¬ 0 < x^2-7*y^2 := fun hh => (not_lt_of_ge h.le) (hn.2.mpr hh)
        exact lt_of_le_of_ne (le_of_not_gt hp) h0
      · intro h
        have h0 : lowerHistoryQuadSign u v 3 ≠ 0 := fun hh => (ne_of_lt h) (hn.1.mp hh)
        have hp : ¬ 0 < lowerHistoryQuadSign u v 3 := fun hh => (not_lt_of_ge h.le) (hn.2.mp hh)
        exact lt_of_le_of_ne (le_of_not_gt hp) h0
    constructor
    · rw [neg_eq_zero, hn.1, ← he, mul_eq_zero, or_iff_left hc.ne]
    · rw [neg_pos, hnn, ← he]
      constructor
      · intro h; nlinarith
      · intro h; exact mul_neg_of_pos_of_neg h hc

#print axioms solution
