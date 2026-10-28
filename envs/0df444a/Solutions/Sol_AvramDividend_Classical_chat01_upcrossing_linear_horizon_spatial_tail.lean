-- Prove2me | solution 1 for AvramDividend.Classical.chat01_upcrossing_linear_horizon_spatial_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:38:12.304383+00:00
-- url     : https://prove2.me/submissions/03900980-decb-4249-830d-997fc8e0203f

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_chat01_finite_horizon_upcrossing_probability_explicit_tail
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Finite-horizon upper crossing is exponentially unlikely when the spatial
    gap dominates twice the time-discount exponent. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) (A : Set Ω)
    (hAmeas : MeasurableSet A)
    (hA : A ⊆ {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)})
    (t : ℝ) (htime : ∀ ω ∈ A, ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t)
    (hlinear : 2 * (q * t) ≤ φ * z) :
    P A ≤ ENNReal.ofReal (Real.exp (-(φ * z) / 2)) := by
  have htail := chat01_finite_horizon_upcrossing_probability_explicit_tail
    X q hq φ hφ hroot z hz A hAmeas hA t htime
  have hexp : q * t - φ * z ≤ -(φ * z) / 2 := by
    linarith
  exact htail.trans (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr hexp))

