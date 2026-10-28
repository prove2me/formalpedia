-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_esscher_root_of_notBV
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:30:23.819641+00:00
-- url     : https://prove2.me/submissions/4e26fdd9-332a-4c49-95ec-779375c28fc6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_continuous_root_from_growth
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero
import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (hnbv : ¬ X.BoundedVariation) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q := by
  obtain ⟨β₀, hβ₀, hgt⟩ := chat04_psi_eventually_gt_of_unbounded_variation X q hq hnbv
  obtain ⟨φ, hφ, _, hroot⟩ :=
    positive_continuous_root_from_growth X.ψ q (β₀ + 1) hq (by linarith)
      (levy_laplace_exponent_continuousOn_nonnegative X)
      (levy_laplace_exponent_zero X) (hgt _ (by linarith))
  exact ⟨φ, hφ, hroot⟩
