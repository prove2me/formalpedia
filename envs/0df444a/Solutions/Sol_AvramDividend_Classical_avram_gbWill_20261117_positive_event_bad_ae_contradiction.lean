-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbWill_20261117_positive_event_bad_ae_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T21:59:52.892543+00:00
-- url     : https://prove2.me/submissions/8a1b2e31-6394-4c17-a56d-5aa720c7a509

import Mathlib.MeasureTheory.Measure.Restrict
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
noncomputable section
/-- Positive bad-event mass contradicts a global a.e. assertion. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (E : Set Ω)
    (hMeas : MeasurableSet E) (hPos : 0 < P E)
    (Good Bounded : Ω → Prop)
    (hBound : ∀ᵐ ω ∂(P.restrict E), Bounded ω)
    (hBad : ∀ ω ∈ E, Bounded ω → ¬ Good ω) :
    ¬ ∀ᵐ ω ∂P, Good ω := by
  intro hGood
  have hGoodE : ∀ᵐ ω ∂(P.restrict E), Good ω :=
    ae_restrict_of_ae hGood
  have hMemE : ∀ᵐ ω ∂(P.restrict E), ω ∈ E :=
    ae_restrict_mem hMeas
  have hFalse : ∀ᵐ ω ∂(P.restrict E), False := by
    filter_upwards [hGoodE, hBound, hMemE] with ω hg hb he
    exact (hBad ω he hb) hg
  letI : (ae (P.restrict E)).NeBot :=
    (ae_restrict_neBot).2 (ne_of_gt hPos)
  obtain ⟨ω, hω⟩ := hFalse.exists
  exact hω
