-- Prove2me | solution 1 for AvramDividend.Classical.bv_supported_stationary_fubini_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T11:58:12.211451+00:00
-- url     : https://prove2.me/submissions/c7a60e45-0498-4f02-abfa-4ffd2c46385c

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Restrict

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter

theorem solution
    {T Ω : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
    (μ : Measure T) (P : Measure Ω)
    [SFinite μ] [SFinite P] [NeZero μ]
    (B : Set T) (hSupport : ∀ᵐ t ∂μ, t ∈ B)
    (t₀ : T) (A : T → Ω → Prop)
    (hMeas : MeasurableSet {z : T × Ω | A z.1 z.2})
    (hPath : ∀ᵐ ω ∂P, ∀ᵐ t ∂μ, A t ω)
    (hStationary : ∀ t ∈ B,
      (∀ᵐ ω ∂P, A t ω) ↔ (∀ᵐ ω ∂P, A t₀ ω)) :
    ∀ᵐ ω ∂P, A t₀ ω := by
  have hSwap : ∀ᵐ t ∂μ, ∀ᵐ ω ∂P, A t ω :=
    (Measure.ae_ae_comm hMeas).mpr hPath
  have hBoth : ∀ᵐ t ∂μ,
      t ∈ B ∧ (∀ᵐ ω ∂P, A t ω) := by
    filter_upwards [hSupport, hSwap] with t ht hs
    exact ⟨ht, hs⟩
  obtain ⟨t, htB, htA⟩ := hBoth.exists
  exact (hStationary t htB).mp htA
