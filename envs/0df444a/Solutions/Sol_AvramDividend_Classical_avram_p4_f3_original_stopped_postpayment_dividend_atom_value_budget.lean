-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_stopped_postpayment_dividend_atom_value_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:18:43.654377+00:00
-- url     : https://prove2.me/submissions/c899fb6c-bdfe-4e48-837c-87a7078a4302

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

/-- The original clock secant budget pays the right dividend atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℝ≥0)
    (hTime : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    w (x + X.X t ω - rightLimit D t ω) +
      (rightLimit D t ω - D t ω) ≤
        w (riskProcess X x D t ω) := by
  have hAtom := hjump ω t hTime
  have hPost :=
    (avram_wave7_18_original_riskProcess_postpayment_rightjump_decomposition
      X x D hD ω t).1
  rw [hPost] at hAtom
  linarith
