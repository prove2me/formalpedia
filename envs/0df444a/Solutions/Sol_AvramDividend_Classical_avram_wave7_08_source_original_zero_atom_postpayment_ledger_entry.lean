-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:46:39.989758+00:00
-- url     : https://prove2.me/submissions/a193552d-d424-46c2-9acb-b35499a837f7

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) :
    w (x - rightLimit D 0 ω) + rightLimit D 0 ω ≤ w x := by
  have hD0 : D 0 ω = 0 := hD.1.1.1 ω
  have hX0 : X.X 0 ω = 0 := X.X_zero ω
  have h := hjump ω 0 (Or.inl rfl)
  simp only [riskProcess, hD0, hX0, sub_zero, add_zero] at h
  linarith
