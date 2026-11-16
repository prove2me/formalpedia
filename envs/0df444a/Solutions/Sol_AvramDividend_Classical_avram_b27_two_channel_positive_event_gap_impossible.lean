-- Prove2me | solution 1 for AvramDividend.Classical.avram_b27_two_channel_positive_event_gap_impossible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:17:45.494727+00:00
-- url     : https://prove2.me/submissions/023628d5-9baa-47e5-a637-7455dc2fd529

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b26_no_large_jump_event_L1_cash_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped Topology

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (F W : Ω → ℝ) (G J E : ℕ → Ω → ℝ)
    (hFI : Integrable F (P.restrict A))
    (hWI : Integrable W (P.restrict A))
    (hGI : ∀ n, Integrable (G n) (P.restrict A))
    (hJI : ∀ n, Integrable (J n) (P.restrict A))
    (hEI : ∀ n, Integrable (E n) P)
    (hGmean : ∀ n, (∫ ω in A, G n ω ∂P) = 0)
    (hJmean : ∀ n, (∫ ω in A, J n ω ∂P) = 0)
    (hEL1 : Tendsto
      (fun n => ∫ ω, ‖E n ω‖ ∂P) atTop (𝓝 (0 : ℝ)))
    (hCash : ∀ n, ∀ᵐ ω ∂(P.restrict A),
      F ω ≤ W ω + G n ω + J n ω + E n ω)
    (δ : ℝ) (hδ : 0 < δ)
    (hGap : (∫ ω in A, W ω ∂P) + δ ≤
      (∫ ω in A, F ω ∂P)) : False := by
  let K : ℕ → Ω → ℝ := fun n ω => G n ω + J n ω
  have hKI (n : ℕ) : Integrable (K n) (P.restrict A) :=
    (hGI n).add (hJI n)
  have hKmean (n : ℕ) : (∫ ω in A, K n ω ∂P) = 0 := by
    change (∫ ω in A, G n ω + J n ω ∂P) = 0
    rw [integral_add (hGI n) (hJI n), hGmean n, hJmean n]
    ring
  have hKcash : ∀ n, ∀ᵐ ω ∂(P.restrict A),
      F ω ≤ W ω + K n ω + E n ω := by
    intro n
    filter_upwards [hCash n] with ω hω
    change F ω ≤ W ω + (G n ω + J n ω) + E n ω
    linarith
  have hBudget :=
    AvramDividend.Classical.avram_b26_no_large_jump_event_L1_cash_budget
      P A hA F W K E hFI hWI hKI hEI hKmean hEL1 hKcash
  linarith
