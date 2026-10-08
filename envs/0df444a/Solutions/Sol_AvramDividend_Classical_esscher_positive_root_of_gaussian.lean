-- Prove2me | solution 1 for AvramDividend.Classical.esscher_positive_root_of_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:34:09.019748+00:00
-- url     : https://prove2.me/submissions/efd91091-bdf9-4271-9fe6-72acb98666e5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_gaussian
import Theorems.Thm_AvramDividend_Classical_positive_continuous_root_from_growth

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Positive Esscher root in the Gaussian case from proved exponent growth and IVT. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hσ : 0 < X.σ)
    (hcont : ContinuousOn X.ψ (Ici (0 : ℝ))) (hzero : X.ψ 0 = 0) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q := by
  obtain ⟨β₀, hβnonneg, hβgt⟩ :=
    psi_eventually_gt_of_gaussian X q hσ
  let A : ℝ := max β₀ 1
  have hApos : 0 < A :=
    lt_of_lt_of_le (by norm_num) (le_max_right β₀ 1)
  have hψA : q < X.ψ A := hβgt A (le_max_left β₀ 1)
  obtain ⟨φ, hφpos, hφle, hφeq⟩ :=
    positive_continuous_root_from_growth X.ψ q A hq hApos hcont hzero hψA
  exact ⟨φ, hφpos, hφeq⟩
