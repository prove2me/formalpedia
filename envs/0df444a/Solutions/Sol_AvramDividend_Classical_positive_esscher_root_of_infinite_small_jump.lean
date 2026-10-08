-- Prove2me | solution 1 for AvramDividend.Classical.positive_esscher_root_of_infinite_small_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:42:59.144563+00:00
-- url     : https://prove2.me/submissions/7613973d-d89d-4b39-b6f7-d8d35a3fc33c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_of_infinite_small_jump
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
    (hσ : X.σ = 0)
    (hinf : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (q : ℝ) (hq : 0 < q) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q :=
  esscher_positive_root_of_infinite_small_jump X hσ hinf q hq
    (levy_laplace_exponent_continuousOn_nonnegative X)
    (levy_laplace_exponent_zero X)
