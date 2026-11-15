-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a285_first_order_discount_expected_energy_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:34:36.476977+00:00
-- url     : https://prove2.me/submissions/1bb2eaaa-17d1-4dad-8c24-16009272bb47

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S E : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (η K : ℝ) (hη : 0 ≤ η)
    (hSI : ∀ m, Integrable (S m) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hExpected : ∀ m, (∫ ω, E m ω ∂P) ≤ K)
    (hPt : ∀ m ω, S m ω ≤ η*E m ω+a m)
    (hRate : Tendsto a atTop (𝓝 (0:ℝ))) :
    ∀ ζ, 0 < ζ → ∃ k : ℕ, ∀ m, k ≤ m →
      (∫ ω, S m ω ∂P) ≤ η*K+ζ := by
  intro ζ hζ
  have hEvent : ∀ᶠ m : ℕ in atTop, a m < ζ :=
    (tendsto_order.1 hRate).2 ζ hζ
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 hEvent
  refine ⟨k, ?_⟩
  intro m hm
  have hI : Integrable (fun ω => η * E m ω + a m) P :=
    ((hEI m).const_mul η).add (integrable_const _)
  have hBound : (∫ ω, S m ω ∂P) ≤
      (∫ ω, η * E m ω + a m ∂P) :=
    integral_mono (hSI m) hI (hPt m)
  have hInt : (∫ ω, η * E m ω + a m ∂P) =
      η * (∫ ω, E m ω ∂P) + a m := by
    rw [integral_add ((hEI m).const_mul η) (integrable_const _),
      integral_const_mul]
    simp
  rw [hInt] at hBound
  have hMul := mul_le_mul_of_nonneg_left (hExpected m) hη
  linarith [hk m hm]
