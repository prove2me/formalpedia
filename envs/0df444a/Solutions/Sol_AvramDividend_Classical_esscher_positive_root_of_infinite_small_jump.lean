-- Prove2me | solution 1 for AvramDividend.Classical.esscher_positive_root_of_infinite_small_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:08:34.17033+00:00
-- url     : https://prove2.me/submissions/8a3c01c1-f6de-4df9-a625-2f79480fdd21

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_positive_continuous_root_from_growth

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Construct a positive Esscher root in the infinite-small-jump case
from established large-parameter exponent growth and generic IVT. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0)
    (hinf : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (q : ℝ) (hq : 0 < q)
    (hcont : ContinuousOn X.ψ (Ici (0 : ℝ))) (hzero : X.ψ 0 = 0) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q := by
  obtain ⟨β₀, hβnonneg, hβgt⟩ :=
    psi_eventually_gt_of_infinite_small_jump_moment X hσ hinf q hq
  let A : ℝ := max β₀ 1
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) (le_max_right β₀ 1)
  have hψA : q < X.ψ A := hβgt A (le_max_left β₀ 1)
  obtain ⟨φ, hφpos, hφle, hφroot⟩ :=
    positive_continuous_root_from_growth X.ψ q A hq hApos hcont hzero hψA
  exact ⟨φ, hφpos, hφroot⟩
