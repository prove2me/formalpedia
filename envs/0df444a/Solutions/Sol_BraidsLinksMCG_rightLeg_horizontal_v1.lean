-- Prove2me | solution 1 for BraidsLinksMCG.rightLeg_horizontal_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T00:15:30.880865+00:00
-- url     : https://prove2.me/submissions/98802e02-7f28-458f-8749-140a386b63b2

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

open Set

/-- The punctures of `PuncturedPlane (n+1)`, spelled as the `Set.range` used by
the ambient half-plane theorems. -/
def punctureRange (n : ℕ) : Set ℂ :=
  Set.range (fun j : Fin (n + 1) => (((j : ℕ) + 1 : ℕ) : ℂ))

/-- The punctured right half-plane: real part strictly above `n + 1/2`, minus the
`n+1` real punctures. -/
def rightAmbient (n : ℕ) : Set ℂ :=
  {z : ℂ | (n : ℝ) + 1 / 2 < z.re} ∩ (punctureRange n)ᶜ

/-- The real part of the `j`-th puncture, in the exact `Set.range` shape. -/
theorem puncture_re' {n : ℕ} {j : Fin (n + 1)} :
    ((↑(j.val + 1) : ℕ) : ℂ).re = 1 + (j.val : ℝ) := by
  rw [Nat.cast_add, Nat.cast_one, add_comm]
  norm_num

/-- The bridge between the two spellings of a puncture: `Set.range` writes
`((↑j + 1 : ℕ) : ℂ)` while the `PuncturedPlane` predicate writes
`((j : ℕ) + 1 : ℂ)`.  `Nat.cast_add`/`Nat.cast_one` make them equal. -/
theorem cast_puncture (j : ℕ) :
    ((j : ℕ) + 1 : ℂ) = (((j : ℕ) + 1 : ℕ) : ℂ) := by norm_num

/-- The imaginary part of the `j`-th puncture is zero: every puncture is real. -/
theorem puncture_im' {n : ℕ} {j : Fin (n + 1)} :
    ((↑(j.val + 1) : ℕ) : ℂ).im = 0 := by
  simp

/-- Beta-reduce the equation produced by `Set.mem_range` after `rintro ⟨j, hj⟩`;
`exact` avoids `simpa`'s one-sided normalisation, which fails to close here. -/
theorem beta_puncture {n : ℕ} {w : ℂ} {j : Fin (n + 1)}
    (hj : (fun k : Fin (n + 1) => (((k : ℕ) + 1 : ℕ) : ℂ)) j = w) :
    ((↑(j.val + 1) : ℕ) : ℂ) = w := by
  show (fun k : Fin (n + 1) => (((k : ℕ) + 1 : ℕ) : ℂ)) j = w
  exact hj

/-- The hub's real part `n + 3/4` is not an integer `j + 1`, so a segment of
constant real part `n + 3/4` meets no puncture. -/
theorem three_quarters_ne {n : ℕ} {j : Fin (n + 1)} :
    (n : ℝ) + 3 / 4 ≠ 1 + (j.val : ℝ) := by
  intro h
  -- Work in ℕ so integrality is not lost: clear the quarters by multiplying by 4.
  have h4 : (4 * n + 3 : ℕ) = 4 * (j.val + 1) := by
    have h4' : (4 : ℝ) * (n : ℝ) + 3 = 4 * ((j.val : ℝ) + 1) := by linarith
    exact_mod_cast h4'
  omega

/-- A segment between two points of real part `> r` stays in that half-plane. -/
theorem segment_re_gt {x y : ℂ} {r : ℝ} (hx : r < x.re) (hy : r < y.re) :
    segment ℝ x y ⊆ {c : ℂ | r < c.re} := (convex_halfSpace_re_gt r).segment_subset hx hy

/-- Membership in `rightAmbient`, from the real-part bound and puncture exclusion. -/
theorem mem_rightAmbient {n : ℕ} {z : ℂ}
    (hzre : (n : ℝ) + 1 / 2 < z.re)
    (hnot : z ∈ (punctureRange n)ᶜ) : z ∈ rightAmbient n :=
  ⟨hzre, hnot⟩

/-- The hub: real part `n + 3/4`, height `1`.  Its real part is non-integral, so
the vertical leg of the two-leg construction misses every puncture. -/
noncomputable def hub (n : ℕ) : ℂ := (n : ℝ) + 3 / 4 + 1 * Complex.I

/-- The real part of the corner point `(n + 3/4) + z.im * I`. -/
theorem corner_re (n : ℕ) (z : ℂ) :
    ((n : ℝ) + 3 / 4 + z.im * Complex.I).re = (n : ℝ) + 3 / 4 := by
  simp

/-- The real part of the top point `z.re + 1 * I`. -/
theorem top_re (z : ℂ) : (z.re + 1 * Complex.I).re = z.re := by
  simp

/-- The imaginary part of the corner point `(n + 3/4) + z.im * I`. -/
theorem corner_im (n : ℕ) (z : ℂ) :
    ((n : ℝ) + 3 / 4 + z.im * Complex.I).im = z.im := by
  simp

/-- On the vertical segment from `z` to `z.re + 1 * I`, a point of imaginary
part `0` is the initial endpoint `z` itself.  This is what makes case `im z = 0`
safe: the vertical leg meets the real axis only at `z`, which is not a puncture. -/
theorem vertical_im_zero {z : ℂ} (hz0 : z.im = 0) {w : ℂ}
    (hw : w ∈ segment ℝ z (z.re + 1 * Complex.I)) (hwim0 : w.im = 0) : w = z := by
  rw [segment_eq_image ℝ z (z.re + 1 * Complex.I)] at hw
  obtain ⟨t, ht, heq⟩ := hw
  have heq' : (1 - t) • z + t • (z.re + 1 * Complex.I) = w := by
    show (fun θ : ℝ => (1 - θ) • z + θ • (z.re + 1 * Complex.I)) t = w
    exact heq
  have him : w.im = t := by
    have h1 : (t • (z.re + 1 * Complex.I)).im = t := by
      rw [Complex.smul_im, smul_eq_mul, Complex.add_im]
      simp only [Complex.ofReal_im, one_mul, Complex.I_im, zero_add]
      ring
    have h0 := congrArg Complex.im heq'
    rw [Complex.add_im, h1] at h0
    rw [Complex.smul_im, smul_eq_mul, hz0, mul_zero, zero_add] at h0
    rw [h0, hwim0]
  have ht0 : t = 0 := by rw [← him]; exact hwim0
  rw [ht0] at heq'
  simp only [sub_zero, one_smul, zero_smul, add_zero] at heq'
  exact heq'.symm

/-- A coordinate of a segment between two points agreeing in that coordinate is
constant along the segment.  `f` must commute with addition and with real
scaling, which is what `Complex.re` and `Complex.im` do.  Both coordinate
constancy facts below are instances of this single argument. -/
theorem segment_coord_eq (f : ℂ → ℝ) (hfadd : ∀ u v, f (u + v) = f u + f v)
    (hfsmul : ∀ (t : ℝ) (u : ℂ), f (t • u) = t * f u) {x y : ℂ} (hxy : f x = f y)
    {w : ℂ} (hw : w ∈ segment ℝ x y) : f w = f x := by
  rw [segment_eq_image ℝ x y] at hw
  obtain ⟨t, ht, heq⟩ := hw
  have heq' : (1 - t) • x + t • y = w := by
    show (fun θ : ℝ => (1 - θ) • x + θ • y) t = w
    exact heq
  have h := congrArg f heq'
  rw [hfadd, hfsmul, hfsmul, ← hxy] at h
  calc f w = (1 - t) * f x + t * f x := by linarith
        _ = f x := by ring

/-- The horizontal segment from `z` to a point of equal imaginary part keeps that
imaginary part.  Used to show such a segment misses every real puncture when the
shared imaginary part is nonzero. -/
theorem segment_im_eq {x y : ℂ} (hxy : x.im = y.im) {w : ℂ}
    (hw : w ∈ segment ℝ x y) : w.im = x.im :=
  segment_coord_eq Complex.im
    (fun u v => (Complex.add_im u v).symm)
    (fun t u => by rw [Complex.smul_im, smul_eq_mul]) hxy hw

/-- The vertical segment from `x` to a point of equal real part keeps that real
part.  Used to rule out a puncture on a segment of constant real part. -/
theorem segment_re_eq {x y : ℂ} (hxy : x.re = y.re) {w : ℂ}
    (hw : w ∈ segment ℝ x y) : w.re = x.re :=
  segment_coord_eq Complex.re
    (fun u v => (Complex.add_re u v).symm)
    (fun t u => by rw [Complex.smul_re, smul_eq_mul]) hxy hw

/-- The shared body of all three legs: the segment from `x` to `y` stays in the
right half-plane by convexity of its endpoints, and `hcontra` rules out every
puncture on it.  Folding the skeleton in once keeps the `Set.mem_range`
beta-redex handling (`beta_puncture`) in a single place.  `hcontra` is
parameterised by the puncture in `Set.range` form, which is exactly the
beta-redex that `rintro ⟨j, hj⟩` produces. -/
theorem leg (n : ℕ) {x y : ℂ} (hx : (n : ℝ) + 1 / 2 < x.re) (hy : (n : ℝ) + 1 / 2 < y.re)
    (hcontra : ∀ j : Fin (n + 1), ∀ w : ℂ,
      w ∈ segment ℝ x y → (((j : ℕ) + 1 : ℕ) : ℂ) = w → False) :
    JoinedIn (rightAmbient n) x y := by
  refine JoinedIn.of_segment_subset ?_
  intro w hw
  refine mem_rightAmbient (segment_re_gt hx hy hw) ?_
  rintro ⟨j, hj⟩
  exact hcontra j w hw (beta_puncture hj)

/-- A HORIZONTAL leg: the segment from `x` to `y` has constant imaginary part, so
if that common imaginary part is nonzero the segment misses every puncture, since
every puncture is real.  Shared body of the two horizontal legs. -/
theorem leg_horiz (n : ℕ) {x y : ℂ} (hxy : x.im = y.im) (hx : (n : ℝ) + 1 / 2 < x.re)
    (hy : (n : ℝ) + 1 / 2 < y.re) (hne : x.im ≠ 0) : JoinedIn (rightAmbient n) x y := by
  refine leg n hx hy (fun j w hw hj => ?_)
  have hwim0 : w.im = 0 := by rw [← hj, puncture_im']
  rw [segment_im_eq hxy hw] at hwim0
  exact absurd hwim0 hne

end BraidsLinksMCG

theorem solution (n : ℕ) (x y : ℂ)
    (hxy : x.im = y.im) (hne : x.im ≠ 0)
    (hx : (n : ℝ) + 1 / 2 < x.re) (hy : (n : ℝ) + 1 / 2 < y.re) :
    JoinedIn
        ({z : ℂ | (n : ℝ) + 1 / 2 < z.re} ∩
          (Set.range (fun j : Fin (n + 1) => (((j : ℕ) + 1 : ℕ) : ℂ)))ᶜ)
        x y :=
  BraidsLinksMCG.leg_horiz n hxy hx hy hne
