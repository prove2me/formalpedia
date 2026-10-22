-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_contDiff_one_gaussian_without_standing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T09:37:37.741753+00:00
-- url     : https://prove2.me/submissions/ea3b0315-b8b2-422a-b2b5-7452a84e70d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_scale_absolute_continuity
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_gaussian

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
# The `q`-scale function is `C¹` on the positive axis when `σ > 0`

Chan–Kyprianou–Savov (2011) and Avram–Palmowski–Pistorius (2007, Condition
(3.3) and Lemma 2(i)): a spectrally negative Lévy process with a strictly
positive Gaussian coefficient has a `q`-scale function that is continuously
differentiable on the strictly positive half-line.  **No standing
assumption is needed** -- in particular no integrability of the first moment
of the positive part, and no `Condition (3.3)`.

## The reduction

The proof composes the mission's own Proved results with one imported Open
child, the in-scope leaf

    unbounded_tilted_scale_absolute_continuity  (0883e459)

whose statement is exactly that the **Esscher-tilted** scale function
`V x = e^{-φ x} W x` is `C¹` on the positive half-line, for a positive
Esscher root `φ` with `ψ φ = q`, under the hypothesis `¬ X.BoundedVariation`
-- which `0 < X.σ` implies, since `BoundedVariation` forces `X.σ = 0`.
Note that `0883e459` itself carries no standing hypothesis, which is exactly
what this target needs.

The remaining step is elementary: on the positive axis

    W x = e^{φ x} · V x,

and the product of two `C¹` functions is `C¹`.  The exponential
`x ↦ e^{φ x}` is `C¹` by `Real.contDiff_exp` and `ContDiffOn.const_smul`,
and the product rule for `ContDiffOn` is `ContDiffOn.mul`.

## What this candidate is, and is not

The imported child `0883e459` is still **Open**.  Its content is the
Wiener–Hopf / absolute-continuity step: the Stieltjes measure of the
Esscher-tilted function `V` must be shown to be absolutely continuous, so
that `V` has a continuous density.  So this candidate is a source-faithful
*reduction*, not a proof; it is expected to return `SKETCH_ACCEPTED`, and
the target stays `Open` until the imported child is discharged.

The reduction is worth recording because it shortens the chain to the goal
markedly: `0883e459` (this target's child) feeds the `C¹` regularity, which
feeds `44b032f3` (generator integrability) and then the goal's aggregator
`e8fbc763`, and hence the goal `88d146b8` itself.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  -- Step 1: a positive Esscher root.  This is the Gaussian case, so the
  -- standing-free Proved theorem applies.
  obtain ⟨φ, hφ, hroot⟩ := positive_esscher_root_of_gaussian X q hq hσ
  -- Step 2: a strictly positive Gaussian coefficient excludes the
  -- bounded-variation case, because `BoundedVariation` forces `X.σ = 0`.
  have hnbv : ¬ X.BoundedVariation := by
    intro hbv
    have hσzero : X.σ = 0 := hbv.1
    have hposσ : (0 : ℝ) < X.σ := hσ
    rw [hσzero] at hposσ
    exact absurd hposσ (by norm_num)
  -- Step 3: the Esscher-tilted scale function.
  let V : ℝ → ℝ := fun x => Real.exp (-(φ * x)) * W x
  have hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x := by
    intro x hx
    rfl
  -- Step 4: the tilted function is `C¹` on the positive axis.
  have hVdiff : ContDiffOn ℝ 1 V (Ioi 0) :=
    unbounded_tilted_scale_absolute_continuity X q hq W hW hnbv φ hφ hroot V hV
  -- Step 5: the exponential factor is `C¹` on the positive axis.
  have hexp : ContDiffOn ℝ 1 (fun x : ℝ => Real.exp (φ * x)) (Ioi 0) := by
    -- `x ↦ e^{φ x}` is `e` composed with the `C¹` function `x ↦ φ * x`,
    -- and `x ↦ φ * x` is the constant `φ` times the identity.
    have hlin : ContDiff ℝ 1 (fun x : ℝ => φ * x) := by
      have hconst : ContDiff ℝ 1 (fun _ : ℝ => (φ : ℝ)) :=
        contDiff_const (𝕜 := ℝ) (E := ℝ) (F := ℝ) (c := φ)
      have hid : ContDiff ℝ 1 (fun x : ℝ => x) := contDiff_id
      simpa only [Pi.one_apply, one_mul] using
        (ContDiff.mul (f := fun _ : ℝ => (φ : ℝ)) (g := fun x : ℝ => x) hconst hid)
    have hone : ContDiff ℝ 1 (fun x : ℝ => Real.exp (φ * x)) := by
      have hc : ContDiff ℝ 1 (Real.exp : ℝ → ℝ) := Real.contDiff_exp
      -- `ContDiff.comp` takes the outer function's `ContDiff` first.
      simpa only [Function.comp_def] using
        (ContDiff.comp (f := fun x : ℝ => φ * x) hc hlin)
    exact hone.contDiffOn
  -- Step 6: their product is `C¹`, and on the positive axis the product is `W`.
  have hprod : ContDiffOn ℝ 1 (fun x : ℝ => Real.exp (φ * x) * V x) (Ioi 0) :=
    ContDiffOn.mul hexp hVdiff
  have hpoint : ∀ x : ℝ, 0 < x → Real.exp (φ * x) * V x = W x := by
    intro x hx
    simp only [V, mul_assoc]
    have hexp0 : Real.exp (φ * x) * Real.exp (-(φ * x)) = 1 := by
      rw [← Real.exp_add]
      simp only [add_neg_cancel, Real.exp_zero]
    rw [← mul_assoc, hexp0, one_mul]
  refine hprod.congr (fun x hx => ?_)
  rw [hpoint x hx]
