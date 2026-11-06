-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_postpayment_rightatom_value_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:17:14.751226+00:00
-- url     : https://prove2.me/submissions/6e19be9f-4230-487b-9088-e68dea57d8e3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_riskProcess_postpayment_rightjump_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original right-dividend atom is paid from prepayment value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0), True →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℝ≥0) :
    w (x + X.X t ω - rightLimit D t ω) +
      (rightLimit D t ω - D t ω) ≤
        w (riskProcess X x D t ω) := by
  have hAtom := hjump ω t trivial
  have hPost :=
    (avram_wave7_18_original_riskProcess_postpayment_rightjump_decomposition
      X x D hD ω t).1
  rw [hPost] at hAtom
  linarith
