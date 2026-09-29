-- Prove2me | solution 1 for BraidsLinksMCG.leftHalfPlane_ambient_pathConnected_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-26T17:17:57.413564+00:00
-- url     : https://prove2.me/submissions/e705fd97-9c4b-4b06-af31-a87ff90f25a2

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

-- The punctured left half-plane is path connected in the ambient plane.
-- Target `BraidsLinksMCG.leftHalfPlane_ambient_pathConnected_v1`.
--
-- Every puncture `((j:Nat)+1 : C)` is real with real part at least `1`.  Each
-- point of `W` is joined to the anchor `i`: one segment when `im z > 0` or
-- `im z = 0`, and two through `-i` when `im z < 0`.  Half-plane containments
-- come from `Convex.segment_subset`; puncture avoidance is pointwise, since a
-- uniform distance bound would be false.

open Set

namespace BraidsLinksMCG

/-- The ambient left half-plane with the `n+1` punctures removed. -/
def W (n : ℕ) : Set ℂ := {z : ℂ | z.re < (n : ℝ) + 1} ∩
  (Set.range (fun j : Fin (n + 1) => (((j : ℕ) + 1 : ℕ) : ℂ)))ᶜ

private theorem i_re : Complex.I.re = 0 := Complex.I_re
private theorem negI_re : (-Complex.I).re = 0 := by simp [Complex.neg_re]
private theorem negI_im : (-Complex.I).im = -1 := by simp [Complex.neg_im]

/-- A segment between two points of real part `< r` stays in that half-plane. -/
private theorem segment_re {x y : ℂ} {r : ℝ} (hx : x.re < r) (hy : y.re < r) :
    segment ℝ x y ⊆ {c : ℂ | c.re < r} := (convex_halfSpace_re_lt r).segment_subset hx hy

private theorem segment_im_lt {x y : ℂ} {r : ℝ} (hx : x.im < r) (hy : y.im < r) :
    segment ℝ x y ⊆ {c : ℂ | c.im < r} := (convex_halfSpace_im_lt r).segment_subset hx hy

private theorem segment_im_gt {x y : ℂ} {r : ℝ} (hx : r < x.im) (hy : r < y.im) :
    segment ℝ x y ⊆ {c : ℂ | r < c.im} := (convex_halfSpace_im_gt r).segment_subset hx hy

/-- Membership in `W n`, given the real-part bound and puncture exclusion. -/
private theorem w_of {n : ℕ} {z : ℂ} (hzre : z.re < (n : ℝ) + 1)
    (hnot : z ∈ (Set.range (fun j : Fin (n + 1) => (((j : ℕ) + 1 : ℕ) : ℂ)))ᶜ) : z ∈ W n :=
  ⟨hzre, hnot⟩

/-- The anchor's real part satisfies the half-plane bound, and so does every
point of the imaginary axis. -/
private theorem axis_re_lt {n : ℕ} {z : ℂ} (hz : z.re = 0) : z.re < (n : ℝ) + 1 := by
  rw [hz]
  have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- Beta-reduce the equation produced by `Set.mem_range` after
`rintro ⟨j, hj⟩`.  Using `exact` avoids running the simp set over one side
only, which is what `simpa` does and why it fails to close here. -/
private theorem beta_puncture {n : ℕ} {w : ℂ} {j : Fin (n + 1)}
    (hj : (fun k : Fin (n + 1) => (((k : ℕ) + 1 : ℕ) : ℂ)) j = w) :
    ((↑(j.val + 1) : ℕ) : ℂ) = w := by
  show (fun k : Fin (n + 1) => (((k : ℕ) + 1 : ℕ) : ℂ)) j = w
  exact hj

/-- The imaginary part of the `j`-th puncture, stated over `Fin` so the rewrite
key is exactly the `↑(↑j + 1)` that the goals carry. -/
private theorem puncture_im' {n : ℕ} {j : Fin (n + 1)} : ((↑(j.val + 1) : ℕ) : ℂ).im = 0 := by
  show Complex.im (Complex.ofReal ((j.val + 1 : ℕ) : ℝ)) = 0; exact Complex.ofReal_im _

/-- The real part of the `j`-th puncture, in the same shape. -/
private theorem puncture_re' {n : ℕ} {j : Fin (n + 1)} :
    ((↑(j.val + 1) : ℕ) : ℂ).re = 1 + (j.val : ℝ) := by
  show Complex.re (Complex.ofReal ((j.val + 1 : ℕ) : ℝ)) = 1 + (j.val : ℝ)
  rw [Complex.ofReal_re, Nat.cast_add, Nat.cast_one, add_comm]

private theorem mem_W_iff {n : ℕ} {z : ℂ} (a : z ∈ W n) :
    z.re < (n : ℝ) + 1 ∧ z ∈ (Set.range (fun j : Fin (n + 1) => (((j : ℕ) + 1 : ℕ) : ℂ)))ᶜ :=
  ⟨a.1, a.2⟩

theorem i_mem_W (n : ℕ) : Complex.I ∈ W n := by
  refine w_of (axis_re_lt i_re) ?_
  rintro ⟨j, hj⟩
  have h2 := congrArg Complex.im hj
  simp at h2

theorem negI_mem_W (n : ℕ) : -Complex.I ∈ W n := by
  refine w_of (axis_re_lt negI_re) ?_
  rintro ⟨j, hj⟩
  have h2 := congrArg Complex.im hj
  simp at h2

/-- Every point of `W n` is joined to the anchor `i` within `W n`. -/
theorem joined_anchor {n : ℕ} {z : ℂ} (hz : z ∈ W n) :
    JoinedIn (W n) z Complex.I := by
  rcases mem_W_iff hz with ⟨hzre, hznot⟩
  rcases lt_trichotomy z.im 0 with hlt | hz0 | hgt
  · -- `im z < 0`: descend in the lower half-plane, then climb the axis.
    have hlow : JoinedIn (W n) z (-Complex.I) := by
      apply JoinedIn.of_segment_subset
      intro w hw
      have hseg : segment ℝ z (-Complex.I) ⊆ {c : ℂ | c.im < 0} :=
        segment_im_lt hlt (by norm_num)
      have himw : w.im < 0 := hseg hw
      refine ⟨segment_re hzre (axis_re_lt negI_re) hw, ?_⟩
      rintro ⟨j, hj⟩
      have hjw : w = ((↑(j.val + 1) : ℕ) : ℂ) := (beta_puncture hj).symm
      rw [hjw, puncture_im'] at himw
      norm_num at himw
    have haxis : JoinedIn (W n) (-Complex.I) Complex.I := by
      apply JoinedIn.of_segment_subset
      intro w hw
      refine ⟨segment_re (axis_re_lt negI_re) (axis_re_lt i_re) hw, ?_⟩
      rintro ⟨j, hj⟩
      have hwre : w.re = 0 := by
        rw [segment_eq_image ℝ (-Complex.I) Complex.I] at hw
        obtain ⟨t, -, heq⟩ := hw
        rw [← heq]
        simp
      -- `w.re = 0` but a puncture has real part `1 + j ≥ 1`.
      rw [← beta_puncture hj, puncture_re'] at hwre
      have h0 : (0 : ℝ) ≤ (j.val : ℝ) := Nat.cast_nonneg j.val
      linarith
    exact hlow.trans haxis
  · -- `im z = 0`: the only real point of `[z -[ℝ] i]` is `z`, a non-puncture.
    apply JoinedIn.of_segment_subset
    intro w hw
    refine ⟨segment_re hzre (axis_re_lt i_re) hw, ?_⟩
    rintro ⟨j, hj⟩
    have hwz : w = z := by
      rw [segment_eq_image ℝ z Complex.I] at hw
      obtain ⟨t, ht, heq⟩ := hw
      have heq' : (1 - t) • z + t • Complex.I = w := by
        show (fun θ : ℝ => (1 - θ) • z + θ • Complex.I) t = w; exact heq
      have ht0 : t = 0 := by
        have himw : w.im = t := by
          have h := congrArg Complex.im heq'
          rw [Complex.add_im, Complex.smul_im, Complex.real_smul, hz0] at h
          norm_num at h
          linarith
        have : w.im = 0 := by
          rw [← beta_puncture hj]
          exact puncture_im' (j := j)
        rw [← himw, this]
      rw [ht0] at heq'
      simpa using heq'.symm
    exact hznot ⟨j, hj.trans hwz⟩
  · -- `0 < im z`: the segment stays in the open upper half-plane.
    apply JoinedIn.of_segment_subset
    intro w hw
    refine ⟨segment_re hzre (axis_re_lt i_re) hw, ?_⟩
    rintro ⟨j, hj⟩
    have hseg : segment ℝ z Complex.I ⊆ {c : ℂ | (0 : ℝ) < c.im} :=
      segment_im_gt hgt (by norm_num)
    have himw : (0 : ℝ) < w.im := hseg hw
    have hj' : ((↑(j.val + 1) : ℕ) : ℂ) = w := beta_puncture hj
    rw [← hj', puncture_im'] at himw
    norm_num at himw

theorem leftHalfPlane_pathConnected (n : ℕ) : IsPathConnected (W n) :=
  ⟨Complex.I, i_mem_W n, fun y hy => (joined_anchor (n := n) (z := y) hy).symm⟩

end BraidsLinksMCG

theorem solution (n : ℕ) :
    IsPathConnected
      ({z : ℂ | z.re < ((n : ℝ) + 1 : ℝ)} ∩
        (Set.range (fun j : Fin (n + 1) => (((j : ℕ) + 1 : ℕ) : ℂ)))ᶜ) :=
  BraidsLinksMCG.leftHalfPlane_pathConnected n
