-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_integrable_centered_jump_plus_HJB_cash_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:30:44.220122+00:00
-- url     : https://prove2.me/submissions/89473ced-d378-4b2a-8ffe-03121ca61290

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- An original-path compensated source jump term with genuine L1 mean zero
can be added to an integrable nonpositive HJB drift without losing the
expected signed cash bound. This is an assembly lemma, conditional on both
named source-proved inputs, and asserts no new compensator identity. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M B : Ω → ℝ)
    (hM : Integrable M P ∧ (∫ ω, M ω ∂P) = 0)
    (hB : Integrable B P ∧ (∫ ω, B ω ∂P) ≤ 0) :
    Integrable (fun ω => M ω + B ω) P ∧
      (∫ ω, M ω + B ω ∂P) ≤ 0 := by
  constructor
  · exact hM.1.add hB.1
  · rw [integral_add hM.1 hB.1]
    linarith [hM.2, hB.2]
