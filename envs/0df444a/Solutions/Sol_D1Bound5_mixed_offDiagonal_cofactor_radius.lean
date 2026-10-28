-- Prove2me | solution 1 for D1Bound5.mixed_offDiagonal_cofactor_radius
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:05.731213+00:00
-- url     : https://prove2.me/submissions/a4c9f0e2-ffe0-402f-adb4-37de61171c40

import Lean.Util.CollectAxioms
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5







end D1Bound5


namespace D1Bound5

/-- Cubic cofactor perturbation bound with six independent error radii. -/
theorem _root_.solution (x y z u v w : ℂ)
    (rx ry rz ru rv rw : ℝ)
    (hrx : 0 ≤ rx) (hry : 0 ≤ ry) (hrz : 0 ≤ rz)
    (hru : 0 ≤ ru) (hrv : 0 ≤ rv) (hrw : 0 ≤ rw)
    (hx : ‖x-(1/2 : ℂ)‖ ≤ rx)
    (hy : ‖y-(1/2 : ℂ)‖ ≤ ry)
    (hz : ‖z-(1/2 : ℂ)‖ ≤ rz)
    (hu : ‖u-(1/2 : ℂ)‖ ≤ ru)
    (hv : ‖v-(1/2 : ℂ)‖ ≤ rv)
    (hw : ‖w-(1/2 : ℂ)‖ ≤ rw) :
    ‖w^2*x-w*z*u-w*y*v+(1/8 : ℂ)‖ ≤
      (rx+rz+ru+ry+rv)/4 +
      rw*(rx+(rz+ru+ry+rv)/2) +
      (rw^2+rz*ru+ry*rv)/2 +
      rw*(rx*rw+rz*ru+ry*rv) := by
  let a : ℂ := x-1/2
  let b : ℂ := z-1/2
  let c : ℂ := u-1/2
  let d : ℂ := y-1/2
  let e : ℂ := v-1/2
  let f : ℂ := w-1/2
  have ha : ‖a‖ ≤ rx := hx
  have hb : ‖b‖ ≤ rz := hz
  have hc : ‖c‖ ≤ ru := hu
  have hd : ‖d‖ ≤ ry := hy
  have he : ‖e‖ ≤ rv := hv
  have hf : ‖f‖ ≤ rw := hw
  have hpair (p q : ℂ) (rp rq : ℝ) (hrp : 0 ≤ rp)
      (hp : ‖p‖ ≤ rp) (hq : ‖q‖ ≤ rq) :
      ‖p*q‖ ≤ rp*rq := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hp (norm_nonneg q)).trans
      (mul_le_mul_of_nonneg_left hq hrp)
  have hff : ‖f^2‖ ≤ rw^2 := by
    simpa only [pow_two] using hpair f f rw rw hrw hf hf
  have hbc : ‖b*c‖ ≤ rz*ru := hpair b c rz ru hrz hb hc
  have hde : ‖d*e‖ ≤ ry*rv := hpair d e ry rv hry hd he
  have haf : ‖a*f‖ ≤ rx*rw := hpair a f rx rw hrx ha hf
  let B : ℂ := a-b-c-d-e
  let C : ℂ := a-(b+c+d+e)/2
  let D : ℂ := f^2-b*c-d*e
  let T : ℂ := a*f-b*c-d*e
  have hB : ‖B‖ ≤ rx+rz+ru+ry+rv := by
    have h1 := norm_sub_le a b
    have h2 := norm_sub_le (a-b) c
    have h3 := norm_sub_le (a-b-c) d
    have h4 := norm_sub_le (a-b-c-d) e
    dsimp [B]
    linarith only [h1,h2,h3,h4,ha,hb,hc,hd,he]
  have hsum : ‖b+c+d+e‖ ≤ rz+ru+ry+rv := by
    have h1 := norm_add_le b c
    have h2 := norm_add_le (b+c) d
    have h3 := norm_add_le (b+c+d) e
    linarith only [h1,h2,h3,hb,hc,hd,he]
  have hC : ‖C‖ ≤ rx+(rz+ru+ry+rv)/2 := by
    have h1 := norm_sub_le a ((b+c+d+e)/2)
    have h2 : ‖(b+c+d+e)/2‖ ≤ (rz+ru+ry+rv)/2 := by
      have hnorm : ‖(b+c+d+e)/2‖ = ‖b+c+d+e‖/2 := by simp
      rw [hnorm]
      exact div_le_div_of_nonneg_right hsum (by norm_num)
    dsimp [C]
    linarith only [h1,h2,ha]
  have hD : ‖D‖ ≤ rw^2+rz*ru+ry*rv := by
    have h1 := norm_sub_le (f^2-b*c) (d*e)
    have h2 := norm_sub_le (f^2) (b*c)
    dsimp [D]
    linarith only [h1,h2,hff,hbc,hde]
  have hT : ‖T‖ ≤ rx*rw+rz*ru+ry*rv := by
    have h1 := norm_sub_le (a*f-b*c) (d*e)
    have h2 := norm_sub_le (a*f) (b*c)
    dsimp [T]
    linarith only [h1,h2,haf,hbc,hde]
  have hfC : ‖f*C‖ ≤ rw*(rx+(rz+ru+ry+rv)/2) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hf (norm_nonneg C)).trans
      (mul_le_mul_of_nonneg_left hC hrw)
  have hfT : ‖f*T‖ ≤ rw*(rx*rw+rz*ru+ry*rv) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hf (norm_nonneg T)).trans
      (mul_le_mul_of_nonneg_left hT hrw)
  have hid : w^2*x-w*z*u-w*y*v+(1/8 : ℂ) =
      B/4 + f*C + D/2 + f*T := by
    dsimp [B,C,D,T,a,b,c,d,e,f]
    ring
  have htri : ‖B/4 + f*C + D/2 + f*T‖ ≤
      ‖B/4‖ + ‖f*C‖ + ‖D/2‖ + ‖f*T‖ := by
    have h1 := norm_add_le (B/4+f*C+D/2) (f*T)
    have h2 := norm_add_le (B/4+f*C) (D/2)
    have h3 := norm_add_le (B/4) (f*C)
    linarith only [h1,h2,h3]
  have hB4 : ‖B/4‖ ≤ (rx+rz+ru+ry+rv)/4 := by
    have hnorm : ‖B/4‖ = ‖B‖/4 := by simp
    rw [hnorm]
    exact div_le_div_of_nonneg_right hB (by norm_num)
  have hD2 : ‖D/2‖ ≤ (rw^2+rz*ru+ry*rv)/2 := by
    have hnorm : ‖D/2‖ = ‖D‖/2 := by simp
    rw [hnorm]
    exact div_le_div_of_nonneg_right hD (by norm_num)
  rw [hid]
  linarith only [htri,hB4,hfC,hD2,hfT]





end D1Bound5
end
