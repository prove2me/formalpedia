-- Prove2me | solution 1 for AvramDividend.Classical.positive_esscher_root_of_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:42:50.653008+00:00
-- url     : https://prove2.me/submissions/b53dc262-010a-499b-acee-c86705b3f91e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_of_gaussian
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hσ : 0 < X.σ) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q :=
  esscher_positive_root_of_gaussian X q hq hσ
    (levy_laplace_exponent_continuousOn_nonnegative X)
    (levy_laplace_exponent_zero X)
