-- Prove2me | solution 1 for AvramDividend.Classical.bv_equal_event_measure_ae_equiv_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:12:50.752228+00:00
-- url     : https://prove2.me/submissions/f7123c21-4ff7-419a-aac7-2e94d1a25392

import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (A B : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hEqual : P A = P B) :
    (∀ᵐ ω ∂P, ω ∈ A) ↔ (∀ᵐ ω ∂P, ω ∈ B) := by
  have hCompl : P Aᶜ = P Bᶜ := by
    rw [measure_compl hA (measure_ne_top P A),
        measure_compl hB (measure_ne_top P B),
        hEqual]
  constructor
  · intro hAlmostA
    apply ae_iff.mpr
    have hZero : P Aᶜ = 0 := ae_iff.mp hAlmostA
    exact hCompl.symm.trans hZero
  · intro hAlmostB
    apply ae_iff.mpr
    have hZero : P Bᶜ = 0 := ae_iff.mp hAlmostB
    exact hCompl.trans hZero
