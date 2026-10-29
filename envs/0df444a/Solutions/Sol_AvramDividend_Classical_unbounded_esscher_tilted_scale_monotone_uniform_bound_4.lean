-- Prove2me | solution 4 for AvramDividend.Classical.unbounded_esscher_tilted_scale_monotone_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:15:10.049062+00:00
-- url     : https://prove2.me/submissions/05468d7a-131b-4225-b028-62c8b42b8f52

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_exit_decay
import Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_uniform_bound_of_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set MeasureTheory
open scoped NNReal ENNReal

/-!
The exponentially tilted q-scale function is monotone and bounded
provided the first-passage scale comparison holds.  The one remaining
Open imported theorem is the precise stochastic input to this reduction.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    MonotoneOn V (Ioi (0 : ℝ)) ∧
      ∃ C : ℝ, ∀ x : ℝ, 0 < x → V x ≤ C := by
  have hdecay : ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-φ * (y - x)) * W y :=
    unbounded_esscher_root_exit_decay X q hq W hW hnbv φ hφ hroot
  have hmonoW : MonotoneOn
      (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi (0 : ℝ)) :=
    exit_decay_implies_tilted_monotone W φ hdecay
  have hmonoV : MonotoneOn V (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    simpa only [hV x hx, hV y hy, neg_mul] using hmonoW hx hy hxy
  refine ⟨hmonoV, Real.exp 2 * (φ / q), ?_⟩
  exact esscher_tilted_uniform_bound_of_monotone X q hq W hW φ hφ hroot V hV hmonoV
