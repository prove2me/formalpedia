-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_tilted_positive_monotone
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:46:34.407974+00:00
-- url     : https://prove2.me/submissions/e3dfe4b5-245a-44fe-beb3-619ae0f3b3bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_esscher_exponential_derivative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The excursion logarithmic derivative identity implies the positive
Esscher-normalised scale function is nondecreasing, with no renewal potential
construction. This has one genuine Open stochastic import. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  obtain ⟨φ, μ, hφ, hnull, hfin, hdiff, hrepr⟩ :=
    scaleFunction_excursion_tail_derivative_representation
      X hX q hq W hW
  let g : ℝ → ℝ := fun x => Real.exp (-φ * x) * W x
  have hGdiff : DifferentiableOn ℝ g (Ioi (0 : ℝ)) := by
    intro x hx
    have he : DifferentiableAt ℝ (fun t : ℝ => Real.exp (-φ * t)) x := by
      fun_prop
    exact (he.mul (hdiff x hx)).differentiableWithinAt
  have hGcont : ContinuousOn g (Ioi (0 : ℝ)) := hGdiff.continuousOn
  have hGnonneg : ∀ x : ℝ, 0 < x → 0 ≤ deriv g x := by
    intro x hx
    have he : DifferentiableAt ℝ
        (fun y : ℝ => Real.exp (-φ * y)) x := by
      fun_prop
    have hprod :
        deriv g x =
          deriv (fun y : ℝ => Real.exp (-φ * y)) x * W x +
            Real.exp (-φ * x) * deriv W x := by
      change deriv ((fun y : ℝ => Real.exp (-φ * y)) * W) x = _
      exact deriv_mul he (hdiff x hx)
    have hexpDeriv :
        deriv (fun y : ℝ => Real.exp (-φ * y)) x =
          Real.exp (-φ * x) * (-φ) :=
      esscher_exponential_derivative φ x
    have hmainEq :
        deriv g x = (Real.exp (-φ * x) * (-φ)) * W x +
          Real.exp (-φ * x) * deriv W x := by
      rw [hprod, hexpDeriv]
    have hform :
        deriv g x = (Real.exp (-φ * x) * W x) * μ.real (Ici x) := by
      rw [hmainEq, hrepr x hx]
      ring
    rw [hform]
    exact mul_nonneg
      (mul_nonneg (by positivity) (hW.2.1 x hx.le))
      measureReal_nonneg
  have hGmono : MonotoneOn g (Ioi (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ))
    · exact hGcont
    · simpa only [interior_Ioi] using hGdiff
    · intro x hx
      rw [interior_Ioi] at hx
      exact hGnonneg x hx
  refine ⟨?_, φ, hφ, ?_⟩
  · exact scaleFunction_strict_pos_of_standing X hX q hq W hW
  · exact hGmono
