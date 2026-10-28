-- Prove2me | solution 1 for AvramDividend.Classical.vanishing_expected_deficit_bound_forces_null_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:20:19.028982+00:00
-- url     : https://prove2.me/submissions/44e10182-ad74-48f2-b39a-b55256f73ed1

import Theorems.Thm_AvramDividend_Classical_zero_integral_positive_deficit_event_null
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter

/-- Any vanishing sequence of mesh bounds excludes survival on a nonzero-deficit event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (E : Set Ω) (D : Ω → ℝ)
    (hD : ∀ᵐ ω ∂P, 0 ≤ D ω)
    (hAtom : P {ω : Ω | D ω = 0} = 0)
    (hInt : Integrable (E.indicator D) P)
    (b : ℕ → ℝ) (hb : Tendsto b atTop (nhds (0 : ℝ)))
    (hBound : ∀ n : ℕ,
      (∫ ω, E.indicator D ω ∂P) ≤ b n) :
    P E = 0 := by
  have hUpper : (∫ ω, E.indicator D ω ∂P) ≤ (0 : ℝ) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hb
      (Filter.Eventually.of_forall hBound)
  have hNonneg : ∀ᵐ ω ∂P, 0 ≤ E.indicator D ω := by
    filter_upwards [hD] with ω hω
    by_cases hE : ω ∈ E
    · simpa only [Set.indicator_of_mem hE] using hω
    · simp only [Set.indicator_of_notMem hE, le_refl]
  have hLower : (0 : ℝ) ≤ (∫ ω, E.indicator D ω ∂P) :=
    integral_nonneg_of_ae hNonneg
  have hIntegral : (∫ ω, E.indicator D ω ∂P) = 0 :=
    le_antisymm hUpper hLower
  exact zero_integral_positive_deficit_event_null
    P E D hD hAtom hInt hIntegral
