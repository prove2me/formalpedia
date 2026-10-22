-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_contDiff_two_of_gaussian
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T01:12:48.123099+00:00
-- url     : https://prove2.me/submissions/783ef39e-2927-44e2-bf26-3a3bd3faddb0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_excursion_integrated_scale_representation
import Theorems.Thm_AvramDividend_Classical_excursion_integral_scale_derivative
import Theorems.Thm_AvramDividend_Classical_deriv_eq_zero_of_atomless_cumulative
import Theorems.Thm_AvramDividend_Classical_contDiffOn_two_of_deriv_eq_product_of_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
# The `q`-scale function is `C²` on the positive axis when `σ > 0`

This is the Brownian-smoothing regularity of Chan–Kyprianou–Savov (2011) and
Avram–Palmowski–Pistorius (2007, eq. (3.3) and the Lemma 4 discussion): the
`q`-scale function of a spectrally negative Lévy process with strictly
positive Gaussian coefficient is twice continuously differentiable on the
strictly positive half-line.

## The route

**The excursion-height measure.**  The authoritative in-scope child
`unbounded_esscher_excursion_integrated_scale_representation` (`49acdc06`)
supplies, in one statement, the excursion-height measure `μ` of the
Esscher-tilted scale function, its atomlessness, the finiteness of its
`Ici`-cumulative on every half-line, the continuity of that cumulative, and
the exponential representation

    W b = W a * Real.exp (∫ t in a..b, φ + μ.real (Ici t)).

**The derivative identity.**  The Proved `excursion_integral_scale_derivative`
(`5b518605`) turns the exponential representation into the pointwise
derivative identity

    HasDerivAt W (W x * (φ + μ.real (Ici x))) x            (x > 0).

**The `C²` assembly.**  The child
`contDiffOn_two_of_deriv_eq_product_of_continuous` (`f6a251b4`) packages the
product-rule assembly: if `W` is continuous, `g` is continuous, `W' = W g`
and `g' = 0` on the positive axis, then `W` is `C²` there.

**The vanishing derivative of the cumulative.**  The child
`deriv_eq_zero_of_atomless_cumulative` (`89f1f433`, published by this
session) says that the derivative of the `Ici`-cumulative of an atomless
measure vanishes, because the derivative of a distribution function is its
measure in the Lebesgue sense and an atomless measure has no atoms.

## The repair of candidate 12988

The previous source for this target was rejected with `CE` in six
independent groups.  Each group was a type-level defect, and each is
addressed here without changing the mathematical route.

* `ContinuousOn.add` needs both summands continuous on the *same* set.
  `hμcont` is continuous on `Ioi 0` while `continuous_const.continuousOn`
  is continuous on `univ`, so the constant term is first restricted with
  `ContinuousOn.mono` to `Ioi 0`.
* `deriv_eq_zero_of_atomless_cumulative` takes the cumulative identity
  `hcum : ∀ x, 0 < x → mu.real (Ici x) = g x` as an explicit argument before
  returning `∀ x, 0 < x → deriv g x = 0`.  The previous source passed the
  positivity hypothesis where `hcum` was expected.  Here `hcum` is the
  definitional identity `mu.real (Ici x) = (fun t => mu.real (Ici t)) x`,
  closed by `rfl`.
* `Pi.zero_add` is not a declaration of the pinned Mathlib revision (the
  triage index reports `INDEX_MISS`).  The derivative of the tilt factor is
  instead discharged with `deriv_const_add`, which identifies
  `deriv (fun t => φ + μ.real (Ici t)) x` with
  `deriv (fun t => μ.real (Ici t)) x`, and the vanishing of the latter.
* The `C²` assembly lemma takes `ContinuousOn W (Ioi 0)` as its second
  argument.  The previous source passed a `∀ x hx, ...` lambda, which is a
  `Prop` where a `Type` was expected, and that lambda projected `hy.2` from
  a hypothesis of unknown type.  Here the continuity on `Ioi 0` is obtained
  directly from `hW.2.2.1` by `ContinuousOn.mono`, using `Ioi 0 ⊆ Ici 0`.

## What this candidate is, and is not

The imported in-scope child `49acdc06` (the excursion-height measure and the
exponential representation) is the genuinely analytic input and is still
**Open**, so this source is a source-faithful *reduction* of the target onto
it and the target stays Open until it is discharged.

`49acdc06` is also the source of the differentiability of `W` on the
positive axis that the Proved barrier normaliser
`scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone` (`19cae668`) needs,
and therefore of the non-zero barrier normaliser `hk` that the goal's
aggregator `e8fbc763` requires.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ContDiffOn ℝ 2 W (Ioi 0) := by
  -- `BoundedVariation` forces `X.σ = 0`, which contradicts the Gaussian
  -- hypothesis, so the excursion representation applies.
  have hnbv : ¬ X.BoundedVariation := by
    intro hbv
    have hσzero : X.σ = 0 := hbv.1
    have hposσ : (0 : ℝ) < X.σ := hσ
    rw [hσzero] at hposσ
    exact absurd hposσ (by norm_num)
  -- The excursion-height measure and the exponential representation.
  obtain ⟨φ, μ, hφ, hμ, hμfin, hμcont, hexp⟩ :=
    unbounded_esscher_excursion_integrated_scale_representation
      X q hq W hW hnbv
  -- The pointwise derivative identity.
  have hderiv : ∀ x : ℝ, 0 < x →
      HasDerivAt W (W x * (φ + μ.real (Ici x))) x :=
    excursion_integral_scale_derivative W φ μ hμcont hexp
  -- The scale function is continuous on `[0, ∞)`.
  have hWcont : ContinuousOn W (Ici 0) := hW.2.2.1
  -- The scale function is continuous on the strictly positive half-line, which
  -- is what the `C²` assembly lemma asks for.
  have hWcontIoi : ContinuousOn W (Ioi (0 : ℝ)) :=
    hWcont.mono Ioi_subset_Ici_self
  -- The tilt factor `g x = φ + μ.real (Ici x)` is continuous on the positive axis.
  have hgcont : ContinuousOn (fun x : ℝ => φ + μ.real (Ici x)) (Ioi 0) := by
    -- `ContinuousOn.add` builds the sum in the order of its two arguments,
    -- so the constant is added on the right; `add_comm` puts it on the left
    -- where the tilt factor needs it.
    have hsum : ContinuousOn (fun x : ℝ => μ.real (Ici x) + φ) (Ioi 0) :=
      hμcont.add (continuousOn_const (s := Ioi (0 : ℝ)))
    simpa only [add_comm] using hsum
  -- The `Ici`-cumulative of the measure is the cumulative itself.
  have hcum : ∀ x : ℝ, 0 < x → μ.real (Ici x) = (fun t : ℝ => μ.real (Ici t)) x := by
    intro x _
    rfl
  -- The `Ici`-cumulative of the atomless measure has vanishing derivative, and
  -- so has the tilt factor.
  have hcumzero : ∀ x : ℝ, 0 < x → deriv (fun t : ℝ => μ.real (Ici t)) x = 0 :=
    fun x hx => deriv_eq_zero_of_atomless_cumulative μ (fun t : ℝ => μ.real (Ici t))
      hμfin hμcont hcum x hx
  have hgzero : ∀ x : ℝ, 0 < x → deriv (fun t : ℝ => φ + μ.real (Ici t)) x = 0 := by
    intro x hx
    -- `deriv_const_add` identifies the derivative of the constant-plus-cumulative
    -- with the derivative of the cumulative, and `hcumzero` kills the latter.
    have hadd : deriv (fun t : ℝ => φ + μ.real (Ici t)) x
        = deriv (fun t : ℝ => μ.real (Ici t)) x := deriv_const_add φ
    rw [hadd, hcumzero x hx]
  -- The `C²` assembly.
  exact contDiffOn_two_of_deriv_eq_product_of_continuous W
    (fun x : ℝ => φ + μ.real (Ici x)) hWcontIoi hgcont hderiv hgzero
