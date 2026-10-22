-- Prove2me | solution 1 for FullFormalization.hasDerivAt_Hc
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:59:12.008928+00:00
-- url     : https://prove2.me/submissions/92d594a4-3203-4215-a433-1325af47fcf4

-- Generated from F:/20261008/FullFormalization\FullFormalization\LiftedHuber.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.LiftedHuber

  Source sections 25-26: the *common extremal function* of Theorem B.

  Fix `d j = j (j+7) / 8` (4.1) and a unit vector `u`.  With

      c = 1 / (2 d_N + 1)                                           (25.1)
      H_c(t) = t^2/2  for |t| ≤ c,   c |t| - c^2/2  for |t| ≥ c     (25.2)

  the source defines

      f_N(z) = H_c(⟪u,z⟫ - 1) + (1/2) ‖z - ⟪u,z⟫ u‖²                (25.3)

  Section 26 then records:

  * (26.1) the orthogonal decomposition `z = t u + w`, `w ⊥ u`, along which
    `f_N(z) = H_c(t - 1) + (1/2)‖w‖²`;
  * (26.2) the unique minimiser `z* = u`, `f_N* = 0`, `‖z*‖ = 1`;
  * (26.3) the gradient `∇f_N(z) = clip(⟪u,z⟫-1, -c, c) u + (z - ⟪u,z⟫ u)`,
    whose two summands live in the orthogonal subspaces `span u` and `u^⊥` and
    are each 1-Lipschitz, whence `f_N` is convex, differentiable and globally
    1-smooth;
  * (26.4)-(26.6) the linear-branch formulas on `t ≤ 1 - c`.

  Everything below is proved, nothing is postulated.  The single genuinely
  analytic point is `hasDerivAt_Hc`: the Huber function is differentiable
  everywhere, including at the two kinks `t = ±c`, where the quadratic and
  linear branches paste together smoothly.  Those two points are handled by
  gluing the one-sided derivatives with `HasDerivWithinAt.union`.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_LiftedHuber
import Theorems.Thm_FullFormalization_Hc_of_abs_le
import Theorems.Thm_FullFormalization_Hc_of_le_abs
import Theorems.Thm_FullFormalization_clip_eq_max
import Theorems.Thm_FullFormalization_clip_le_left
import Theorems.Thm_FullFormalization_clip_neg
import Theorems.Thm_FullFormalization_clip_pos
import Theorems.Thm_FullFormalization_clip_self

open scoped Gradient RealInnerProductSpace Topology
open Set
open InnerProductSpace

set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### The clipping map of (26.3) -/

















/-! ### The Huber function (25.2) -/













/-! ### Differentiability of the Huber function

The only non-elementary point is `|t| = c`, where the branch is a smooth paste
of `t²/2` and `c|t| - c²/2`: on `Iic c` the function agrees with `t²/2` near
`c`, on `Ici c` it agrees with `c t - c²/2`, and both one-sided derivatives at
`c` equal `c`.  The two one-sided statements are glued with
`HasDerivWithinAt.union`. -/







/-! ### Orthogonal decomposition in the direction `u` -/

















/-! ### The gradient of `H_c(⟪u,·⟫ - 1)` -/



/-! ### The gradient of `(1/2)‖z - ⟪u,z⟫ u‖²` -/



/-! ### The lifted Huber function (25.3) -/











/-! ### The gradient (26.3) -/







/-! ### Convexity, via monotonicity of the gradient -/







/-! ### The gradient is globally 1-Lipschitz

The first summand of (26.3) lies in `span u`, the second in `u^⊥`; the two
components of `a - b` decompose the same way, so Pythagoras reduces the claim to
the 1-Lipschitzness of the clipping. -/



/-! ### The minimum of the lifted Huber function (26.2) -/







/-! ### The linear branch (26.4)-(26.6) -/





/-! ### The source's cutoff, and the specialization to `liftedHuber` -/





























end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace Topology
open Set
open InnerProductSpace
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open FullFormalization in
theorem solution (c : ℝ) (hc : 0 < c) (t : ℝ) :
    HasDerivAt (Hc c) (clip t (-c) c) t := by
  rcases lt_trichotomy t (-c) with hlt | heq | hgt
  · -- `t < -c`: the left linear branch
    have hval : ∀ x ∈ Set.Iio (-c), Hc c x = -c * x - c ^ 2 / 2 := by
      intro x hx
      have hx' : x < -c := hx
      have hx0 : x < 0 := by linarith
      have hcx : c ≤ |x| := by rw [abs_of_neg hx0]; linarith
      rw [Hc_of_le_abs c x hcx, abs_of_neg hx0]
      ring
    have hev : Hc c =ᶠ[𝓝 t] (fun x : ℝ => -c * x - c ^ 2 / 2) :=
      Filter.eventually_of_mem (isOpen_Iio.mem_nhds hlt) fun x hx => hval x hx
    have hd : HasDerivAt (fun x : ℝ => -c * x - c ^ 2 / 2) (-c) t := by
      simpa using ((hasDerivAt_id t).const_mul (-c)).sub_const (c ^ 2 / 2)
    exact (hd.congr_of_eventuallyEq hev).congr_deriv (clip_neg c t (le_of_lt hlt)).symm
  · -- `t = -c`: glue the two one-sided derivatives
    rw [heq, clip_neg c (-c) (le_refl (-c))]
    have hleft : HasDerivWithinAt (Hc c) (-c) (Set.Iic (-c)) (-c) := by
      have hd : HasDerivAt (fun x : ℝ => -c * x - c ^ 2 / 2) (-c) (-c) := by
        simpa using ((hasDerivAt_id (-c)).const_mul (-c)).sub_const (c ^ 2 / 2)
      refine hd.hasDerivWithinAt.congr ?_ ?_
      · intro x hx
        have hx' : x ≤ -c := hx
        have hx0 : x ≤ 0 := by linarith
        have hcx : c ≤ |x| := by rw [abs_of_nonpos hx0]; linarith
        rw [Hc_of_le_abs c x hcx, abs_of_nonpos hx0]
        ring
      · rw [Hc_of_abs_le c (-c) (by rw [abs_neg, abs_of_pos hc])]
        ring
    have hright : HasDerivWithinAt (Hc c) (-c) (Set.Ici (-c)) (-c) := by
      have hd : HasDerivAt (fun x : ℝ => x ^ 2 / 2) (-c) (-c) := by
        have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * (-c)) (-c) := by
          simpa using hasDerivAt_pow 2 (-c)
        have h2 := h1.div_const 2
        rwa [show 2 * (-c) / 2 = -c by ring] at h2
      refine hd.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
      · show ∀ᶠ x in 𝓝[Set.Ici (-c)] (-c), Hc c x = x ^ 2 / 2
        rw [eventually_nhdsWithin_iff]
        refine Filter.eventually_of_mem (isOpen_Iio.mem_nhds (by linarith : -c < c)) ?_
        intro x hx hx2
        have hx2' : -c ≤ x := hx2
        rw [Hc_of_abs_le c x (abs_le.mpr ⟨hx2', le_of_lt hx⟩)]
      · rw [Hc_of_abs_le c (-c) (by rw [abs_neg, abs_of_pos hc])]
    have hglue : HasDerivAt (Hc c) (-c) (-c) := by
      have h := hleft.union hright
      rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at h
      exact h
    exact hglue
  · -- `-c < t`
    rcases lt_trichotomy t c with hlt' | heq' | hgt'
    · -- `-c < t < c`: the quadratic branch
      have hval : ∀ x ∈ Set.Ioo (-c) c, Hc c x = x ^ 2 / 2 := by
        intro x hx
        have hx1 : -c < x := hx.1
        have hx2 : x < c := hx.2
        rw [Hc_of_abs_le c x (abs_le.mpr ⟨le_of_lt hx1, le_of_lt hx2⟩)]
      have hev : Hc c =ᶠ[𝓝 t] (fun x : ℝ => x ^ 2 / 2) :=
        Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨hgt, hlt'⟩) fun x hx => hval x hx
      have hd : HasDerivAt (fun x : ℝ => x ^ 2 / 2) t t := by
        have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
          simpa using hasDerivAt_pow 2 t
        have h2 := h1.div_const 2
        rwa [show 2 * t / 2 = t by ring] at h2
      exact (hd.congr_of_eventuallyEq hev).congr_deriv
        (clip_self c t (abs_le.mpr ⟨le_of_lt hgt, le_of_lt hlt'⟩)).symm
    · -- `t = c`: glue the two one-sided derivatives
      rw [heq', clip_pos c c (le_of_lt hc) (le_refl c)]
      have hright : HasDerivWithinAt (Hc c) c (Set.Ici c) c := by
        have hd : HasDerivAt (fun x : ℝ => c * x - c ^ 2 / 2) c c := by
          simpa using ((hasDerivAt_id c).const_mul c).sub_const (c ^ 2 / 2)
        refine hd.hasDerivWithinAt.congr ?_ ?_
        · intro x hx
          have hx' : c ≤ x := hx
          have hx0 : 0 < x := by linarith
          have hcx : c ≤ |x| := by rw [abs_of_pos hx0]; exact hx'
          rw [Hc_of_le_abs c x hcx, abs_of_pos hx0]
        · rw [Hc_of_abs_le c c (by rw [abs_of_pos hc])]
          ring
      have hleft : HasDerivWithinAt (Hc c) c (Set.Iic c) c := by
        have hd : HasDerivAt (fun x : ℝ => x ^ 2 / 2) c c := by
          have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * c) c := by
            simpa using hasDerivAt_pow 2 c
          have h2 := h1.div_const 2
          rwa [show 2 * c / 2 = c by ring] at h2
        refine hd.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
        · show ∀ᶠ x in 𝓝[Set.Iic c] c, Hc c x = x ^ 2 / 2
          rw [eventually_nhdsWithin_iff]
          refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds (by linarith : -c < c)) ?_
          intro x hx hx2
          have hx2' : x ≤ c := hx2
          rw [Hc_of_abs_le c x (abs_le.mpr ⟨le_of_lt hx, hx2'⟩)]
        · rw [Hc_of_abs_le c c (by rw [abs_of_pos hc])]
      have hglue : HasDerivAt (Hc c) c c := by
        have h := hleft.union hright
        rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at h
        exact h
      exact hglue
    · -- `c < t`: the right linear branch
      have hval : ∀ x ∈ Set.Ioi c, Hc c x = c * x - c ^ 2 / 2 := by
        intro x hx
        have hx' : c < x := hx
        have hx0 : 0 < x := by linarith
        have hcx : c ≤ |x| := by rw [abs_of_pos hx0]; exact le_of_lt hx'
        rw [Hc_of_le_abs c x hcx, abs_of_pos hx0]
      have hev : Hc c =ᶠ[𝓝 t] (fun x : ℝ => c * x - c ^ 2 / 2) :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hgt') fun x hx => hval x hx
      have hd : HasDerivAt (fun x : ℝ => c * x - c ^ 2 / 2) c t := by
        simpa using ((hasDerivAt_id t).const_mul c).sub_const (c ^ 2 / 2)
      exact (hd.congr_of_eventuallyEq hev).congr_deriv
        (clip_pos c t (le_of_lt hc) (le_of_lt hgt')).symm
