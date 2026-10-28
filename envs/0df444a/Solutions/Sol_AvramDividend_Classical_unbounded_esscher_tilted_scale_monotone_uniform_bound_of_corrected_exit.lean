-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_esscher_tilted_scale_monotone_uniform_bound_of_corrected_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:16:23.157497+00:00
-- url     : https://prove2.me/submissions/b58a538e-017d-4b0a-8e16-6c0bf52af99c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_decay_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_uniform_bound_of_monotone
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Corrected killed exits yield a monotone and uniformly bounded Esscher tilt. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    MonotoneOn V (Ioi (0 : ℝ)) ∧
      ∃ C : ℝ, ∀ x : ℝ, 0 < x → V x ≤ C := by
  have hscale := unbounded_fixedroot_decay_of_corrected_exit_identity
    X q hq W hW hnbv φ hφ hroot hExit
  have hraw := exit_decay_implies_tilted_monotone W φ (by
    simpa only [neg_mul] using hscale)
  have htilt : MonotoneOn
      (fun x : ℝ => Real.exp (-(φ * x)) * W x) (Ioi (0 : ℝ)) := by
    simpa only [neg_mul] using hraw
  have hmono : MonotoneOn V (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    rw [hV x hx, hV y hy]
    exact htilt hx hy hxy
  refine ⟨hmono, Real.exp 2 * (φ / q), ?_⟩
  exact esscher_tilted_uniform_bound_of_monotone
    X q hq W hW φ hφ hroot V hV hmono
