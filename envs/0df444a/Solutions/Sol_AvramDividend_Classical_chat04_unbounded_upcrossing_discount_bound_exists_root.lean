-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_upcrossing_discount_bound_exists_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:26:50.843518+00:00
-- url     : https://prove2.me/submissions/8cbf93ca-5252-425a-8155-1d6bfd18fa79

import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_unrestricted_upcrossing_discount_bound
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Positive-root upcrossing discount bound without an assumed Esscher parameter. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (z : ℝ) (hz : 0 ≤ z) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q ∧
      (∫⁻ ω, if twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)
        then ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTimeCorrected X z ω))))
        else 0 ∂P) ≤ ENNReal.ofReal (Real.exp (-(φ * z))) := by
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation X hnbv q hq
  refine ⟨φ, hφ, hroot, ?_⟩
  exact levy_positive_root_unrestricted_upcrossing_discount_bound
    X q hq φ hφ hroot z hz
