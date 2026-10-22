-- Prove2me | solution 1 for FullFormalization.gradient_scaled
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:56:51.3928+00:00
-- url     : https://prove2.me/submissions/576c1787-1e9b-4d57-be3d-70b7631a55a5

-- Generated from F:/20261008/FullFormalization\FullFormalization\Scaling.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.Scaling

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, sections 19 and 32.

  Section 19 ("恢复一般 `L,R`", source lines 1638-1650 of the `### 19.` block) and
  section 32 (source lines 2688-2751) are the same argument in two places: starting
  from a *normalised* function `f_N` (optimiser `u`, initial point `0`, `L = R = 1`)
  one manufactures a general instance by

      f(x) = L R^2 f_N((x - x_init)/R)                                   (32.1)

  and the source records four consequences:

    (i)   ∇f(x) = L R ∇f_N((x - x_init)/R);
    (ii)  ‖∇f(x) - ∇f(y)‖ ≤ L ‖x - y‖                                 (L-smoothness);
    (iii) the optimiser is x⋆ = x_init + R u, at distance R from x_init;
    (iv)  "由于算法均按公开 R 在 normalized coordinates 中运行，归一化轨迹与
          L = R = 1 完全一致，所以所有 q_{A,N} 保持不变" — i.e. the *normalised*
          trajectory (and therefore every normalised loss `q_{A,N}`) is unchanged.

  Representation choices (recorded here because they are genuine formalisation
  decisions, not transcription):

  * `(x - x_init)/R` is written `(1/R) • (x - x_init)`.  Mathlib has no division
    `· / ·` of a vector by a scalar; `1/R` is the reciprocal *scalar* and the two
    expressions are identical field-theoretically.  No other mathematical content
    is hidden in this rewriting.

  * The source's claim (iii) `‖x⋆ - x_init‖ = R` is *not* a consequence of
    admissibility alone: `Admissible 1 1 fN 0 u` only supplies `‖u‖ ≤ 1`
    (this is exactly its `within_radius` field, since the normalized initial point
    is `0`).  What is proved here is the general identity
    `‖(x_init + R • u) - x_init‖ = R * ‖u‖` (`scaled_star_dist`) together with
    the specialisation `= R` under the extra hypothesis `‖u‖ = 1`
    (`scaled_star_dist_eq`).  For the extremisers used in the lower bounds of
    sections 20-31 one has `‖u‖ = 1`, so the source's sentence is recovered
    there; for a general admissible function it would be false (take `f_N = ‖·‖²`,
    `u = 0`).  This is recorded as a *precision* of the source, not a change of
    claim: the sentence is applied in the source only to the extremiser, whose
    `u` does satisfy `‖u‖ = 1`.

  * The transfer of `Admissible`/`AdmissibleUnique` (item (iii)) instantiates the
    admissible class with initial point `x_init` and optimiser `x_init + R • u`.
    Its `within_radius` field then reads `‖x_init - (x_init + R • u)‖ ≤ R`, which is
    exactly the normalised bound `‖u‖ ≤ 1` transported by the scaling — the
    radius hypothesis is *carried along* by the construction rather than added.

  * Item (iv) is formalised as an exact identity between the two trajectories
    (`nagX_scaled`, `nagY_scaled`) plus the exact invariance of the normalised
    loss (`normalizedLoss_scaled`, `normalizedLoss_scaled_nagX`).  This is the
    precise content of "every `q_{A,N}` is unchanged".
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_RationalNAG
import Definitions.Def_Scaling
import Theorems.Thm_FullFormalization_comp_smul_one
import Theorems.Thm_FullFormalization_hasFDerivAt_scaledArg
import Theorems.Thm_FullFormalization_toDual_smul_real

open scoped Gradient

-- Several lemmas below are purely metric/affine and never use completeness of
-- `E` (which the section variable carries because `gradient` requires it).
set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## 1.  The scaling map (32.1) -/





















/-! ## 2.  Gradient scaling (source line 2716)

`∇f(x) = L R ∇f_N((x - x_init)/R)`. -/













/-! ## 3.  Smoothness transfer (source line 2722)

`∀x y, ‖∇f(x) - ∇f(y)‖ ≤ L ‖x - y‖` whenever the normalised gradient is
1-Lipschitz. -/



/-! ## 4.  Differentiability and convexity transfer -/





/-! ## 5.  The optimiser is transported (source lines 2737-2747) -/











/-! ## 6.  Trajectory invariance (source line 2749)

"归一化轨迹与 `L = R = 1` 完全一致" — the scaled trajectory is the affine image of
the normalised one, `k ↦ x_init + R • (normalised iterate)`.  Consequently every
quantity computed on the normalised trajectory (in particular every `q_{A,N}`) is
unchanged. -/







/-! ## 7.  Invariance of the normalised loss `q_{A,N}` (source line 2749) -/







end FullFormalization

open FullFormalization

open scoped Gradient
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open FullFormalization in

theorem solution {L R : ℝ} (_hL : 0 < L) (hR : 0 < R) {x_init : E} {fN : E → ℝ}
    (hd : Differentiable ℝ fN) (x : E) :
    ∇ (scaled L R x_init fN) x = (L * R) • ∇ fN (scaledArg R x_init x) := by
  have hRne : R ≠ 0 := ne_of_gt hR
  set a : E := scaledArg R x_init x
  -- the scalar identity `L R^2 · (1/R) = L R` that turns the constant in front of
  -- the chain rule into the source's `L R`
  have hcoef : (L * R ^ 2) * (1 / R) = L * R := by
    rw [one_div, mul_assoc,
      show R ^ 2 * R⁻¹ = R by rw [sq, mul_assoc, mul_inv_cancel₀ hRne, mul_one]]
  -- derivative of `f_N` at `a`, in the `toDual` form of the Fréchet–Riesz map
  have hfN : HasFDerivAt fN (InnerProductSpace.toDual ℝ E (∇ fN a)) a := by
    have := (hd a).hasFDerivAt
    rwa [← toDual_gradient] at this
  -- chain rule with the affine coordinate change
  have hcomp : HasFDerivAt (fun y : E => fN (scaledArg R x_init y))
      ((InnerProductSpace.toDual ℝ E (∇ fN a)).comp ((1 / R) • (1 : E →L[ℝ] E))) x := by
    simpa [Function.comp_def] using hfN.comp x (hasFDerivAt_scaledArg R x_init x)
  -- the constant `L R^2` in front
  have hfull : HasFDerivAt (scaled L R x_init fN)
      ((L * R ^ 2) •
        ((InnerProductSpace.toDual ℝ E (∇ fN a)).comp ((1 / R) • (1 : E →L[ℝ] E)))) x := by
    show HasFDerivAt (fun y : E => L * R ^ 2 * fN ((1 / R) • (y - x_init))) _ x
    exact hcomp.const_mul (L * R ^ 2)
  -- identify the derivative with `toDual (L R • ∇ fN a)`
  have hval : (L * R ^ 2) •
        ((InnerProductSpace.toDual ℝ E (∇ fN a)).comp ((1 / R) • (1 : E →L[ℝ] E)))
      = InnerProductSpace.toDual ℝ E ((L * R) • ∇ fN a) := by
    rw [comp_smul_one, smul_smul (L * R ^ 2) (1 / R) (InnerProductSpace.toDual ℝ E (∇ fN a)),
      ← toDual_smul_real, hcoef]
  have hfull' : HasFDerivAt (scaled L R x_init fN)
      (InnerProductSpace.toDual ℝ E ((L * R) • ∇ fN a)) x := by
    rwa [hval] at hfull
  have hg : HasGradientAt (scaled L R x_init fN) ((L * R) • ∇ fN a) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact hfull'
  exact hg.gradient
