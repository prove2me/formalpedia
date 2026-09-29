-- Prove2me | solution 1 for BraidsLinksMCG.rightAmbient_pathConnected_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T01:34:54.097986+00:00
-- url     : https://prove2.me/submissions/af79d642-9fa9-4989-bbb5-dde3f77d09eb

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Theorems.Thm_BraidsLinksMCG_rightLeg_horizontal_v1

namespace BraidsLinksMCG

open Set

/--  -/
def punctureRange (n : ℕ) : Set ℂ :=
  Set.range (fun j : Fin (n + 1) => (((j : ℕ) + 1 : ℕ) : ℂ))

/--  -/
def rightAmbient (n : ℕ) : Set ℂ :=
  {z : ℂ | (n : ℝ) + 1 / 2 < z.re} ∩ (punctureRange n)ᶜ

/-- Membership in `rightAmbient`, from the real-part bound and puncture exclusion. -/
theorem mem_rightAmbient {n : ℕ} {z : ℂ}
    (hzre : (n : ℝ) + 1 / 2 < z.re) (hnot : z ∈ (punctureRange n)ᶜ) : z ∈ rightAmbient n :=
  ⟨hzre, hnot⟩

/-- `Set.range` spells a puncture `((↑j + 1 : ℕ) : ℂ)` while `PuncturedPlane` spells it … -/
theorem beta_puncture {n : ℕ} {w : ℂ} {j : Fin (n + 1)}
    (hj : (fun k : Fin (n + 1) => (((k : ℕ) + 1 : ℕ) : ℂ)) j = w) : ((↑(j.val + 1) : ℕ) : ℂ) = w := by
  show (fun k : Fin (n + 1) => (((k : ℕ) + 1 : ℕ) : ℂ)) j = w; exact hj

/-- Every puncture is real. -/
theorem puncture_im' {n : ℕ} {j : Fin (n + 1)} :
    ((↑(j.val + 1) : ℕ) : ℂ).im = 0 := by
  simp

/-- The real part of the `j`-th puncture, in the exact `Set.range` shape. -/
theorem puncture_re' {n : ℕ} {j : Fin (n + 1)} :
    ((↑(j.val + 1) : ℕ) : ℂ).re = 1 + (j.val : ℝ) := by
  rw [Nat.cast_add, Nat.cast_one, add_comm]
  norm_num

/--  -/
theorem segment_witness {x y w : ℂ} (hw : w ∈ segment ℝ x y) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a • x + b • y = w := by exact Set.mem_setOf_eq.mp hw

/-- must commute with addition and with real scaling, which is what `Complex.re` and -/
theorem segment_coord_eq (f : ℂ → ℝ) (hfadd : ∀ u v, f (u + v) = f u + f v)
    (hfsmul : ∀ (t : ℝ) (u : ℂ), f (t • u) = t * f u) {x y : ℂ} (hxy : f x = f y)
    {w : ℂ} (hw : w ∈ segment ℝ x y) : f w = f x := by
  obtain ⟨a, b, ha, hb, hab, heq⟩ := segment_witness hw
  have h := congrArg f heq
  rw [hfadd, hfsmul, hfsmul, ← hxy] at h
  calc f w = a * f x + b * f x := by linarith
        _ = f x := by rw [← add_mul, hab, one_mul]

/-- A segment between two points of real part `> r` stays in that half-plane. -/
theorem segment_re_gt {x y : ℂ} {r : ℝ} (hx : r < x.re) (hy : r < y.re) {w : ℂ}
    (hw : w ∈ segment ℝ x y) : r < w.re :=
  (convex_halfSpace_re_gt r).segment_subset hx hy hw

/--  -/
theorem segment_re_eq {x y : ℂ} (hxy : x.re = y.re) {w : ℂ}
    (hw : w ∈ segment ℝ x y) : w.re = x.re :=
  segment_coord_eq Complex.re
    (fun u v => (Complex.add_re u v).symm)
    (fun t u => by rw [Complex.smul_re, smul_eq_mul]) hxy hw

/-- The imaginary part of the top point `z.re + 1 * I`. -/
theorem top_im (z : ℂ) : (z.re + 1 * Complex.I).im = 1 := by
  rw [Complex.add_im, Complex.ofReal_im, one_mul, Complex.I_im, zero_add]

/-- part `0` is the initial endpoint `z` itself. This is what makes case `im z = 0` -/
theorem vertical_im_zero {z : ℂ} (hz0 : z.im = 0) {w : ℂ}
    (hw : w ∈ segment ℝ z (z.re + 1 * Complex.I)) (hwim0 : w.im = 0) : w = z := by
  obtain ⟨a, b, ha, hb, hab, heq⟩ := segment_witness hw
  have h := congrArg Complex.im heq
  rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul, top_im,
    hz0, mul_zero, zero_add, hwim0] at h
  have hb0 : b = 0 := by linarith
  have ha1 : a = 1 := by linarith
  rw [ha1, hb0, one_smul, zero_smul, add_zero] at heq
  exact heq.symm

/-- right half-plane by convexity of its endpoints, and `hcontra` rules out every puncture … -/
theorem leg (n : ℕ) {x y : ℂ} (hx : (n : ℝ) + 1 / 2 < x.re) (hy : (n : ℝ) + 1 / 2 < y.re)
    (hcontra : ∀ j : Fin (n + 1), ∀ w : ℂ,
      w ∈ segment ℝ x y → (((j : ℕ) + 1 : ℕ) : ℂ) = w → False) :
    JoinedIn (rightAmbient n) x y := by
  refine JoinedIn.of_segment_subset ?_
  intro w hw
  refine ⟨segment_re_gt hx hy hw, ?_⟩
  rintro ⟨j, hj⟩
  exact hcontra j w hw (beta_puncture hj)

/-- constant real part `n + 3/4` meets no puncture. Clearing the quarters by -/
theorem three_quarters_ne {n : ℕ} {j : Fin (n + 1)} :
    (n : ℝ) + 3 / 4 ≠ 1 + (j.val : ℝ) := by
  intro h
  have h4 : (4 * n + 3 : ℕ) = 4 * (j.val + 1) := by
    have h4' : (4 : ℝ) * (n : ℝ) + 3 = 4 * ((j.val : ℝ) + 1) := by linarith
    exact_mod_cast h4'
  omega

/-- `n + 3/4`, so the segment is in the half-plane and avoids every puncture. -/
theorem leg_vert (n : ℕ) {x y : ℂ} (hxy : x.re = (n : ℝ) + 3 / 4)
    (hyr : y.re = (n : ℝ) + 3 / 4) :
    JoinedIn (rightAmbient n) x y := by
  refine leg n (by rw [hxy]; linarith)
    (by rw [hyr]; linarith) (fun j w hw hj => ?_)
  have hwre : w.re = (n : ℝ) + 3 / 4 := by
    have h := segment_re_eq (x := x) (y := y) (hxy.trans hyr.symm) hw
    exact h.trans hxy
  have hne := three_quarters_ne (n := n) (j := j)
  have hwre' := congrArg Complex.re (beta_puncture hj)
  rw [puncture_re'] at hwre'
  exact absurd (hwre'.trans hwre) hne.symm

/-- height `1`. A puncture on this segment would have imaginary part `0`, so -/
theorem leg_vert_axis (n : ℕ) {z : ℂ} (hz : z ∈ rightAmbient n) (hz0 : z.im = 0) :
    JoinedIn (rightAmbient n) z (z.re + 1 * Complex.I) := by
  have hy : (n : ℝ) + 1 / 2 < (z.re + 1 * Complex.I).re := by simpa only [Complex.add_re,
    Complex.ofReal_re, Complex.I_re, one_mul, add_zero] using Set.mem_setOf_eq.mp hz.1
  refine leg n (Set.mem_setOf_eq.mp hz.1) hy (fun j w hw hj => ?_)
  have hwim0 : w.im = 0 := by rw [← hj, puncture_im']
  have hwz : w = z := vertical_im_zero hz0 hw hwim0
  rw [hwz] at hj
  exact hz.2 ⟨j, beta_puncture hj⟩

/--  -/
theorem hub_mem (n : ℕ) : ((n : ℝ) + 3 / 4 + 1 * Complex.I) ∈ rightAmbient n := by
  refine mem_rightAmbient (by rw [show ((n : ℝ) + 3 / 4 + 1 * Complex.I).re = (n : ℝ) + 3 / 4 by simp]; linarith) ?_
  rintro ⟨j, hj⟩
  have h := congrArg Complex.im (beta_puncture hj)
  rw [puncture_im'] at h
  rw [show ((n : ℝ) + 3 / 4 + 1 * Complex.I).im = 1 by simp] at h
  exact absurd h.symm one_ne_zero

/-- the top point `z.re + 1 * I` across to the hub. Both heights are `1`, so the -/
theorem one_lig (n : ℕ) (x : ℂ) (hx : (n : ℝ) + 1 / 2 < x.re) :
    JoinedIn (rightAmbient n) (x.re + 1 * Complex.I) ((n : ℝ) + 3 / 4 + 1 * Complex.I) := by
  simpa only [rightAmbient, punctureRange] using (rightLeg_horizontal_v1 n (x.re + 1 * Complex.I)
    ((n : ℝ) + 3 / 4 + 1 * Complex.I) (by simp) (by simp)
    (by simpa only [Complex.add_re, Complex.ofReal_re, Complex.I_re, one_mul, add_zero] using hx)
    (by simp; linarith))

theorem rightAmbient_pathConnected (n : ℕ) : IsPathConnected (rightAmbient n) := by
  refine ⟨(n : ℝ) + 3 / 4 + 1 * Complex.I, hub_mem n, ?_⟩
  intro z hz
  have hzre : (n : ℝ) + 1 / 2 < (z.1 : ℂ).re := Set.mem_setOf_eq.mp hz.1
  rcases eq_or_ne z.im 0 with hz0 | hz0
  · exact ((leg_vert_axis n hz hz0).trans (one_lig n z hzre)).symm
  · have hleg1 : JoinedIn (rightAmbient n) z ((n : ℝ) + 3 / 4 + z.im * Complex.I) := by
      simpa only [rightAmbient, punctureRange] using
        (rightLeg_horizontal_v1 n z ((n : ℝ) + 3 / 4 + z.im * Complex.I)
          (by simp) hz0 hzre (by simp; linarith))
    have hleg2 : JoinedIn (rightAmbient n) ((n : ℝ) + 3 / 4 + z.im * Complex.I)
        ((n : ℝ) + 3 / 4 + 1 * Complex.I) := leg_vert n (by simp) (by simp)
    exact (hleg1.trans hleg2).symm

end BraidsLinksMCG

theorem solution (n : ℕ) :
    IsPathConnected ({z : ℂ | (n : ℝ) + 1 / 2 < z.re} ∩
      (Set.range (fun j : Fin (n + 1) => (((j : ℕ) + 1 : ℕ) : ℂ)))ᶜ) :=
  BraidsLinksMCG.rightAmbient_pathConnected n
