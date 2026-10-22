-- Prove2me | solution 2 for AvramDividend.Classical.vcstar_scaledW_boundary_smooth_fit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:35:24.790811+00:00
-- url     : https://prove2.me/submissions/ad993bf1-1103-4d3f-979a-24bdd93d3544
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_cstar_positive_boundary_regularity_package
import Theorems.Thm_AvramDividend_Classical_vcstar_first_deriv_smooth_fit_of_nonzero
import Theorems.Thm_AvramDividend_Classical_vcstar_second_deriv_smooth_fit_of_stationary_scale_deriv
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_at_positive_cstar
import Theorems.Thm_AvramDividend_Classical_iteratedDeriv_two_eq_deriv_deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
# Smooth fit of the barrier value and the scaled scale function at `c*`

The mission's `vcstar W` is the candidate barrier value

    vcstar W x = barrierValue W (cstar W).toReal x

and the *scaled* scale function is `z ↦ divE (W z) (scaleDeriv W c*)`, the
function that the barrier value agrees with below the barrier.  The statement
proved here is that the two agree to **second order** at the barrier level
`c* = (cstar W).toReal`:

    deriv (vcstar W) c* = deriv (scaled W) c*

and

    X.σ ^ 2 * iteratedDeriv 2 (vcstar W) c*
      = X.σ ^ 2 * iteratedDeriv 2 (scaled W) c*.

This is the boundary condition of the Avram–Palmowski–Pistorius Lemma 4
discussion: the candidate value must join the scaled scale function with its
first and second derivative continuous at the barrier.

## The reduction

The proof is a three-step assembly of the mission's own results.

**Step 1 — the boundary regularity package.**  The authoritative child

    scaleFunction_cstar_positive_boundary_regularity_package  (760663cc)

supplies, at a finite positive barrier `c*`,

* `hWdiff : ∀ y > 0, DifferentiableAt ℝ W y` — the differentiability of the
  scale function on the positive axis;
* `hWderiv : deriv W c* ≠ 0` — the non-degeneracy of the barrier slope;
* `hWstat : X.σ ≠ 0 → HasDerivAt (deriv W) 0 c*` — the stationarity of the
  scale-function derivative at the barrier in the non-degenerate case.

**Step 2 — the first-order fit.**  The Proved
`vcstar_first_deriv_smooth_fit_of_nonzero` (`ee1ed302`) says that at a finite
positive barrier where `W` is differentiable and `deriv W c* ≠ 0`, the
derivative of the barrier value equals the derivative of the scaled scale
function.  This is the first conjunct, verbatim.

**Step 3 — the second-order fit.**  The Proved
`vcstar_second_deriv_smooth_fit_of_stationary_scale_deriv` (`2e8cdfd8`) says
that the same holds for the second derivatives, provided the scale-function
derivative is stationary at the barrier (`HasDerivAt (deriv W) 0 c*`) and the
barrier value has unit slope there (`deriv (vcstar W) c* = 1`).  The unit
slope is the content of the authoritative child
`vcstar_deriv_eq_one_at_positive_cstar` (`edf21020`): at a finite positive
optimal barrier the candidate value is tangent to the line of slope one,
because the barrier is where `deriv W` attains its positive interior minimum.

**The degenerate case.**  The second conjunct of the target carries the factor
`X.σ ^ 2`.  When `X.σ = 0` — the bounded-variation case, since
`BoundedVariation` is `X.σ = 0 ∧ ...` — that factor annihilates both sides
and the conjunct is `0 = 0`.  So the second-order fit is only needed in the
non-degenerate case, and the split is on `X.σ = 0` rather than on the three
alternatives of `h_smooth`.

The two second derivatives are compared as `iteratedDeriv 2`, and the Proved
`iteratedDeriv_two_eq_deriv_deriv` (`d52088dd`) identifies
`iteratedDeriv 2 f x` with `deriv (deriv f) x`, which is the form in which
`2e8cdfd8` is stated.

## What this candidate is, and is not

The imported children `760663cc` and `edf21020` are still **Open**.  The
first is the boundary regularity of the scale function at a finite positive
barrier; the second is the unit-slope property of the candidate value there.
Both are authoritative statements of the remaining mathematical inputs, so
this source is a source-faithful *reduction* of the target onto them, and not
a proof of the target while they remain Open.

The two *analytic* parts of the target -- that the first derivatives agree,
and that the second derivatives agree -- are discharged here by the Proved
results `ee1ed302` and `2e8cdfd8` respectively, so nothing of the target's
own statement is left open beyond those two children.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    deriv (vcstar W) (cstar W).toReal =
      deriv (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal ∧
    X.σ ^ 2 * iteratedDeriv 2 (vcstar W) (cstar W).toReal =
      X.σ ^ 2 * iteratedDeriv 2 (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal))
        (cstar W).toReal := by
  -- Step 1: the boundary regularity of the scale function at the barrier.
  obtain ⟨hWdiff, hWderiv, hWstat⟩ :=
    scaleFunction_cstar_positive_boundary_regularity_package
      X hX q hq W hW hc hcpos
  -- The barrier level is positive, since `0 < cstar W` and `cstar W < ⊤`.
  have hcpos' : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hcpos) (ne_of_lt hc)
  -- Step 3 (first half): the unit slope of the candidate value at the barrier.
  have hvderiv : deriv (vcstar W) (cstar W).toReal = 1 :=
    vcstar_deriv_eq_one_at_positive_cstar X hX q hq W hW hc hcpos h_smooth
  -- Step 2: the first derivatives agree at the barrier.
  have hfirst : deriv (vcstar W) (cstar W).toReal =
      deriv (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal))
        (cstar W).toReal :=
    vcstar_first_deriv_smooth_fit_of_nonzero W hcpos'
      (hWdiff (cstar W).toReal hcpos') hWderiv
  -- Step 3 (second half): the second derivatives agree at the barrier.
  have hsecond : X.σ ^ 2 * deriv (deriv (vcstar W)) (cstar W).toReal =
      X.σ ^ 2 * deriv (deriv (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal)))
        (cstar W).toReal := by
    by_cases hσ0 : X.σ = 0
    · -- In the bounded-variation case `X.σ = 0`, so the second conjunct of the
      -- target is `0 = 0` and the second-derivative fit is not needed.
      simp [hσ0]
    · -- In the non-degenerate case the Proved second-derivative smooth fit
      -- gives the two second derivatives; multiplying by `X.σ ^ 2` carries it
      -- to the form the target states.
      have hfit : deriv (deriv (vcstar W)) (cstar W).toReal =
          deriv (deriv (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal)))
            (cstar W).toReal :=
        vcstar_second_deriv_smooth_fit_of_stationary_scale_deriv W hcpos'
          hWdiff hWderiv (hWstat hσ0) hvderiv
      exact congrArg (fun t : ℝ => X.σ ^ 2 * t) hfit
  refine ⟨hfirst, ?_⟩
  -- The target compares `iteratedDeriv 2`, and the Proved
  -- `iteratedDeriv_two_eq_deriv_deriv` identifies it with `deriv (deriv ·)`.
  simpa only [iteratedDeriv_two_eq_deriv_deriv] using hsecond
