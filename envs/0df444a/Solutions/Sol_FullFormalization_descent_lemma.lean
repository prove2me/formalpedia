-- Prove2me | solution 1 for FullFormalization.descent_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:37:16.428409+00:00
-- url     : https://prove2.me/submissions/3677e4f3-f421-4704-a3d2-f2e23b489750

-- Generated from F:/20261008/FullFormalization\FullFormalization\SmoothConvex.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.SmoothConvex

  Source section 2: the smooth-convex interpolation residual

      I_{ij} = F_i - F_j - ⟨g_j, x_i - x_j⟩ - (1/2) ‖g_i - g_j‖²  ≥ 0   (2.2)

  and its proof, which the source carries out in full (lines 211-279) rather
  than citing.  Nothing here is an axiom: (2.2) is derived from convexity and
  global 1-Lipschitzness of the gradient, through exactly the two ingredients
  the source uses.

  Source argument (lines 213-277):
    * `φ = f - ⟪g_j, ·⟫` is convex and 1-smooth, and `∇φ(x_j) = 0`, so `x_j`
      minimises `φ`;
    * the descent lemma gives `φ(x_i - ∇φ(x_i)) ≤ φ(x_i) - ½‖∇φ(x_i)‖²`;
    * hence `φ(x_i) - φ(x_j) ≥ ½‖∇φ(x_i)‖²`, which is (2.2).

  The two ingredients are proved here from scratch:

  * `descent_lemma` — for a differentiable `ψ` whose gradient is globally
    1-Lipschitz, `ψ (u - ∇ψ u) ≤ ψ u - ½‖∇ψ u‖²`.  No convexity is used.
    This is the source's `descent lemma` (quoted at line 227).

  * `convexOn_le_gradient` — for convex differentiable `f`,
    `f y ≥ f x + ⟪∇f x, y - x⟫`, which is what makes a zero gradient a global
    minimiser (source line 235: "hence `x_j` is the global minimiser of `φ`").

  Both reduce to one-dimensional calculus along a segment, using Mathlib's
  `ConvexOn.deriv_le_slope` (convexity versus secant slope) and
  `antitoneOn_of_hasDerivWithinAt_nonpos` (a nonpositive derivative makes a
  function antitone), the formal counterpart of integrating the derivative
  bound.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients

open scoped Gradient RealInnerProductSpace
open Set

set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Gradient of a difference, and of `⟪c, ·⟫` -/









/-! ### The first-order condition for convex differentiable functions -/



/-! ### The descent lemma for a 1-smooth function (source line 227) -/



/-! ### Lemma 2.1 -/



end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
open Set
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open FullFormalization in

theorem solution {ψ : E → ℝ} (hd : Differentiable ℝ ψ)
    (hsm : ∀ a b : E, ‖∇ ψ a - ∇ ψ b‖ ≤ ‖a - b‖) (u : E) :
    ψ (u - ∇ ψ u) ≤ ψ u - (1 / 2) * ‖∇ ψ u‖ ^ 2 := by
  set v : E := ∇ ψ u with hv
  set c : ℝ := ‖v‖ ^ 2 with hc
  let K : ℝ → ℝ := fun t => ψ (u - t • v) + (t - t ^ 2 / 2) * c
  let K' : ℝ → ℝ := fun t => -⟪∇ ψ (u - t • v), v⟫ + (1 - t) * c
  have hK0 : K 0 = ψ u := by
    dsimp only [K]
    simp
  have hK1 : K 1 = ψ (u - ∇ ψ u) + (1 / 2) * ‖∇ ψ u‖ ^ 2 := by
    dsimp only [K]
    simp only [one_smul]
    rw [hv] at hc ⊢
    rw [hc]
    norm_num
  have hpath : ∀ t : ℝ, HasDerivAt (fun s : ℝ => u - s • v) (-v) t := by
    intro t
    have h : HasDerivAt (fun s : ℝ => u - s • v) (0 - (1 : ℝ) • v) t :=
      (hasDerivAt_const t u).sub ((hasDerivAt_id t).smul_const v)
    simpa using h
  have hderivWithin : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
      HasDerivWithinAt K (K' t) (interior (Set.Icc (0 : ℝ) 1)) t := by
    intro t _
    have hcomp : HasDerivAt (fun s : ℝ => ψ (u - s • v)) (-⟪∇ ψ (u - t • v), v⟫) t := by
      have h := (hd (u - t • v)).hasFDerivAt.comp_hasDerivAt t (hpath t)
      simp only [Function.comp_def] at h
      rw [← inner_gradient_left] at h
      simpa using h
    have hpoly : HasDerivAt (fun s : ℝ => (s - s ^ 2 / 2) * c) ((1 - t) * c) t := by
      have hfun : (fun s : ℝ => (s - s ^ 2 / 2) * c)
          = fun s : ℝ => c * s - (c / 2) * s ^ 2 := by
        funext s; ring
      rw [hfun]
      have h1 : HasDerivAt (fun s : ℝ => c * s) (c * 1) t := (hasDerivAt_id t).const_mul c
      have h2 : HasDerivAt (fun s : ℝ => (c / 2) * s ^ 2) ((c / 2) * (2 * t)) t := by
        have h := ((hasDerivAt_id t).pow 2).const_mul (c / 2)
        simpa [id_eq, pow_one, mul_one] using h
      have h := h1.sub h2
      have hval : c * 1 - (c / 2) * (2 * t) = (1 - t) * c := by ring
      rw [hval] at h
      exact h
    exact (hcomp.add hpoly).hasDerivWithinAt
  have hcont : ContinuousOn K (Set.Icc (0 : ℝ) 1) := by
    have h1 : Continuous (fun s : ℝ => ψ (u - s • v)) :=
      hd.continuous.comp (continuous_const.sub (continuous_id.smul continuous_const))
    have h2 : Continuous (fun s : ℝ => (s - s ^ 2 / 2) * c) := by fun_prop
    exact (h1.add h2).continuousOn
  have hnonpos : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), K' t ≤ 0 := by
    intro t ht
    rw [interior_Icc] at ht
    have ht0 : 0 < t := ht.1
    have hlip : ‖∇ ψ (u - t • v) - ∇ ψ u‖ ≤ t * ‖v‖ := by
      have h := hsm (u - t • v) u
      have hnorm : ‖u - t • v - u‖ = t * ‖v‖ := by
        have h1 : u - t • v - u = -(t • v) := by abel
        rw [h1, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ht0)]
      rw [hnorm] at h
      exact h
    have hkey : ⟪∇ ψ (u - t • v), v⟫ - ‖v‖ ^ 2 = ⟪∇ ψ (u - t • v) - ∇ ψ u, v⟫ := by
      rw [show ∇ ψ (u - t • v) - ∇ ψ u = ∇ ψ (u - t • v) - v from by rw [hv]]
      rw [inner_sub_left, real_inner_self_eq_norm_sq]
    have hlow : -(t * ‖v‖) * ‖v‖ ≤ ⟪∇ ψ (u - t • v) - ∇ ψ u, v⟫ := by
      have h := abs_real_inner_le_norm (∇ ψ (u - t • v) - ∇ ψ u) v
      rw [abs_le] at h
      nlinarith [h.1, hlip, norm_nonneg v]
    have hge : (1 - t) * ‖v‖ ^ 2 ≤ ⟪∇ ψ (u - t • v), v⟫ := by
      nlinarith [hkey, hlow, sq_nonneg ‖v‖]
    dsimp only [K']
    rw [hc]
    nlinarith [hge]
  have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) 1) hcont hderivWithin
    hnonpos
  have hle : K 1 ≤ K 0 :=
    hanti (left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
      (right_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)) (by norm_num : (0 : ℝ) ≤ 1)
  rw [hK0, hK1] at hle
  linarith
