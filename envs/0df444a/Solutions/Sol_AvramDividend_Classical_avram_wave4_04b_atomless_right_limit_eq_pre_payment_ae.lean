-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_atomless_right_limit_eq_pre_payment_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:58:05.211481+00:00
-- url     : https://prove2.me/submissions/30874f4e-51f2-4999-b20c-74659e1b833d

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightJump_support_countable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ν : Measure ℝ) [NullSingletonClass ν] :
    ∀ᵐ s ∂ν, 0 ≤ s →
      rightLimit D s.toNNReal ω = D s.toNNReal ω := by
  apply ae_iff.mpr
  have hcount :
      Set.Countable {s : ℝ | 0 ≤ s ∧
        rightLimit D s.toNNReal ω ≠ D s.toNNReal ω} :=
    dividendStrategy_rightJump_support_countable D hD ω
  have hzero :
      ν {s : ℝ | 0 ≤ s ∧
        rightLimit D s.toNNReal ω ≠ D s.toNNReal ω} = 0 :=
    hcount.measure_zero ν
  simpa only [_root_.not_imp] using hzero
