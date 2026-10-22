-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_contDiff_one_of_unbounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:20:24.522379+00:00
-- url     : https://prove2.me/submissions/85043001-e222-4877-82c2-9c42418756d2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_excursion_integrated_scale_representation
import Theorems.Thm_AvramDividend_Classical_excursion_integral_scale_derivative
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_deriv_eq_continuous_product_Ioi
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_unbounded_variation_nonpositive_q

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

/-- The q-scale function of a spectrally negative Levy process with unbounded
variation is continuously differentiable on the positive half-line.

The theorem is stated for an arbitrary real `q`, so the proof splits on the
sign of `q`.

In the branch `0 < q` the analytic part is discharged by two Proved theorems:

- `excursion_integral_scale_derivative` turns the integrated exponential
  representation of `W` into the pointwise derivative identity
  `HasDerivAt W (W x * (phi + mu.real (Ici x))) x`;
- `contDiffOn_one_of_deriv_eq_continuous_product_Ioi` turns that identity,
  together with continuity of the logarithmic-derivative coefficient
  `x |-> phi + mu.real (Ici x)`, into `ContDiffOn ℝ 1 W (Ioi 0)`.

The representation itself is the published child
`unbounded_esscher_excursion_integrated_scale_representation`, which needs
`not X.BoundedVariation` alone, with no standing assumption.

In the branch `q ≤ 0` the conclusion is the published child
`scaleFunction_contDiff_one_of_unbounded_variation_nonpositive_q`, which
carries exactly that hypothesis shape.

Both imported children are used as sketch dependencies: they are the
authoritative statements of the two remaining mathematical inputs, and this
source is the source-faithful reduction of the target onto them.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  by_cases hq0 : q ≤ 0
  · exact scaleFunction_contDiff_one_of_unbounded_variation_nonpositive_q
      X q hq0 W hW hnbv
  · have hq : 0 < q := lt_of_not_ge hq0
    obtain ⟨φ, μ, hφ, hnull, hfin, hμcont, hexp⟩ :=
      unbounded_esscher_excursion_integrated_scale_representation
        X q hq W hW hnbv
    have hderiv : ∀ x : ℝ, 0 < x →
        HasDerivAt W (W x * (φ + μ.real (Ici x))) x :=
      excursion_integral_scale_derivative W φ μ hμcont hexp
    have hconst : ContinuousOn (fun _ : ℝ => φ) (Ioi 0) :=
      continuous_const.continuousOn
    have hg : ContinuousOn (fun x : ℝ => φ + μ.real (Ici x)) (Ioi 0) :=
      hconst.add hμcont
    have hderiv' : ∀ x : ℝ, 0 < x →
        HasDerivAt W ((φ + μ.real (Ici x)) * W x) x := by
      intro x hx
      have hx' := hderiv x hx
      have hcomm : W x * (φ + μ.real (Ici x)) = (φ + μ.real (Ici x)) * W x :=
        mul_comm _ _
      rw [hcomm] at hx'
      exact hx'
    exact contDiffOn_one_of_deriv_eq_continuous_product_Ioi W
      (fun x : ℝ => φ + μ.real (Ici x)) hg hderiv'
