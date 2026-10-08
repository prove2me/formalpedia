-- Prove2me | solution 1 for AvramDividend.Classical.additive_convolution_powers_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:46:06.509913+00:00
-- url     : https://prove2.me/submissions/aac95a2f-6ccb-4ffa-96aa-ad851772033e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_convolution_powers

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (κ : Measure ℝ) [SFinite κ]
    (m : ℕ → Measure ℝ)
    (hm0 : m 0 = Measure.dirac 0)
    (hmsucc : ∀ n : ℕ, m (n + 1) = Measure.conv κ (m n))
    (hsf : ∀ n : ℕ, SFinite (m n)) :
    ∀ n : ℕ, m n Set.univ = (κ Set.univ) ^ n := by
  have hκ :
      (∫⁻ x : ℝ,
        ENNReal.ofReal (Real.exp (-(0 : ℝ) * x)) ∂κ) =
        κ Set.univ := by
    simp
  have hpower :=
    positiveLaplace_convolution_powers
      κ m 0 (κ Set.univ) hm0 hmsucc hsf hκ
  intro n
  simpa using hpower n
