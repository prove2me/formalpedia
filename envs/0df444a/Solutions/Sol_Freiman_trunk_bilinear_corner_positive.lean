-- Prove2me | solution 1 for Freiman.trunk_bilinear_corner_positive
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T04:16:35.42026+00:00
-- url     : https://prove2.me/submissions/b3b187aa-4de8-4c9c-a08f-58374836b9f7

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Freiman

theorem solution (R : CertRectangle) (A B D : ℝ) (hR : certRectangleValid R)
    (hc : ∀ i j : Fin 2, 0 < A+B*((trunkCorner R.r0 R.r1 i : ℝ)+trunkCorner R.s0 R.s1 j)+D*trunkCorner R.r0 R.r1 i*trunkCorner R.s0 R.s1 j)
    (r s : ℝ) (hm : certRectangleMem R r s) :
    0 < A+B*(r+s)+D*r*s := by
  obtain ⟨h1, h2⟩ := hR
  obtain ⟨m1, m2, m3, m4⟩ := hm
  have h1' : (R.r0:ℝ) < R.r1 := by exact_mod_cast h1
  have h2' : (R.s0:ℝ) < R.s1 := by exact_mod_cast h2
  have c00 : 0 < A+B*((R.r0:ℝ)+R.s0)+D*R.r0*R.s0 := hc 0 0
  have c10 : 0 < A+B*((R.r1:ℝ)+R.s0)+D*R.r1*R.s0 := hc 1 0
  have c01 : 0 < A+B*((R.r0:ℝ)+R.s1)+D*R.r0*R.s1 := hc 0 1
  have c11 : 0 < A+B*((R.r1:ℝ)+R.s1)+D*R.r1*R.s1 := hc 1 1
  set f00 := A+B*((R.r0:ℝ)+R.s0)+D*R.r0*R.s0 with hf00
  set f10 := A+B*((R.r1:ℝ)+R.s0)+D*R.r1*R.s0 with hf10
  set f01 := A+B*((R.r0:ℝ)+R.s1)+D*R.r0*R.s1 with hf01
  set f11 := A+B*((R.r1:ℝ)+R.s1)+D*R.r1*R.s1 with hf11
  set w00 := ((R.r1:ℝ)-r)*((R.s1:ℝ)-s) with hw00
  set w10 := (r-(R.r0:ℝ))*((R.s1:ℝ)-s) with hw10
  set w01 := ((R.r1:ℝ)-r)*(s-(R.s0:ℝ)) with hw01
  set w11 := (r-(R.r0:ℝ))*(s-(R.s0:ℝ)) with hw11
  have n00 : 0 ≤ w00 := mul_nonneg (by linarith) (by linarith)
  have n10 : 0 ≤ w10 := mul_nonneg (by linarith) (by linarith)
  have n01 : 0 ≤ w01 := mul_nonneg (by linarith) (by linarith)
  have n11 : 0 ≤ w11 := mul_nonneg (by linarith) (by linarith)
  have key : ((R.r1:ℝ)-R.r0)*((R.s1:ℝ)-R.s0)*(A+B*(r+s)+D*r*s)
      = w00*f00 + w10*f10 + w01*f01 + w11*f11 := by
    simp only [hf00, hf10, hf01, hf11, hw00, hw10, hw01, hw11]; ring
  have tot : w00 + w10 + w01 + w11 = ((R.r1:ℝ)-R.r0)*((R.s1:ℝ)-R.s0) := by
    simp only [hw00, hw10, hw01, hw11]; ring
  set m := min (min f00 f10) (min f01 f11) with hm
  have mpos : 0 < m := by
    simp only [hm, lt_min_iff]; exact ⟨⟨c00, c10⟩, ⟨c01, c11⟩⟩
  have l00 : m ≤ f00 := le_trans (min_le_left _ _) (min_le_left _ _)
  have l10 : m ≤ f10 := le_trans (min_le_left _ _) (min_le_right _ _)
  have l01 : m ≤ f01 := le_trans (min_le_right _ _) (min_le_left _ _)
  have l11 : m ≤ f11 := le_trans (min_le_right _ _) (min_le_right _ _)
  have b00 := mul_le_mul_of_nonneg_left l00 n00
  have b10 := mul_le_mul_of_nonneg_left l10 n10
  have b01 := mul_le_mul_of_nonneg_left l01 n01
  have b11 := mul_le_mul_of_nonneg_left l11 n11
  have area : 0 < ((R.r1:ℝ)-R.r0)*((R.s1:ℝ)-R.s0) := mul_pos (by linarith) (by linarith)
  have hsum : ((R.r1:ℝ)-R.r0)*((R.s1:ℝ)-R.s0)*m ≤ ((R.r1:ℝ)-R.r0)*((R.s1:ℝ)-R.s0)*(A+B*(r+s)+D*r*s) := by
    rw [key]
    have : (w00 + w10 + w01 + w11)*m = w00*m + w10*m + w01*m + w11*m := by ring
    rw [← tot, this]
    linarith
  have hpos : 0 < ((R.r1:ℝ)-R.r0)*((R.s1:ℝ)-R.s0)*(A+B*(r+s)+D*r*s) :=
    lt_of_lt_of_le (mul_pos area mpos) hsum
  exact pos_of_mul_pos_right hpos area.le
