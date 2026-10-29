-- Prove2me | solution 20 for AvramDividend.Classical.unbounded_esscher_root_first_passage_scale_decay
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:29:25.463541+00:00
-- url     : https://prove2.me/submissions/719b98e9-7ff3-486b-8005-b4376d881216

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_monotone_uniform_bound
import Theorems.Thm_AvramDividend_Classical_tilted_monotone_implies_exit_decay

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- True-root first-passage scale comparison obtained from the Esscher CDF. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-(φ * (y - x))) * W y := by
  have htilt : MonotoneOn
      (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
    simpa only [neg_mul] using
      (unbounded_esscher_tilted_scale_monotone_uniform_bound
        X q hq W hW hnbv φ hφ hroot
        (fun x : ℝ => Real.exp (-(φ * x)) * W x)
        (by intro x hx; rfl)).1
  simpa only [neg_mul] using
    tilted_monotone_implies_exit_decay W φ htilt
