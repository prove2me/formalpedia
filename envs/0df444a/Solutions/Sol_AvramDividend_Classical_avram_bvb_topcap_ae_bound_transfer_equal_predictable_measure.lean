-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_ae_bound_transfer_equal_predictable_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T13:09:36.419667+00:00
-- url     : https://prove2.me/submissions/bd3bb873-1749-4ff6-bef1-69e412498e42

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

/-- Transfer an almost-everywhere bound between measures agreeing on measurable sets. -/
theorem solution
    {α : Type*} (m₁ m₂ : MeasurableSpace α)
    (μ : @Measure α m₁) (ν : @Measure α m₂)
    (hEq : ∀ A : Set α, MeasurableSet[m₁] A → μ A = ν A)
    (f : α → ℝ) (hf : Measurable[m₁] f)
    (K : ℝ)
    (hBound : ∀ᵐ p ∂ν, |f p| ≤ K) :
    ∀ᵐ p ∂μ, |f p| ≤ K := by
  letI : MeasurableSpace α := m₁
  have hf' : Measurable f := hf
  have hbad : MeasurableSet {a : α | ¬ |f a| ≤ K} := by
    have hs : MeasurableSet {a : α | K < |f a|} :=
      measurableSet_Ioi.preimage hf'.abs
    simpa only [not_le] using hs
  have hnull : ν {a : α | ¬ |f a| ≤ K} = 0 :=
    (ae_iff).mp hBound
  exact (ae_iff).mpr ((hEq _ hbad).trans hnull)
