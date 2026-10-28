-- Prove2me | solution 1 for AvramDividend.Classical.ae_injective_of_pairwise_ae_distinct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:01:19.357042+00:00
-- url     : https://prove2.me/submissions/49edc36e-6797-46ed-9e57-733498302969

import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Probability.IdentDistrib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

theorem solution
    {Ω ι α : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) (τ : ι → Ω → α)
    (hpair : ∀ i j : ι, i ≠ j → ∀ᵐ ω ∂P, τ i ω ≠ τ j ω) :
    ∀ᵐ ω ∂P, Function.Injective (fun i : ι => τ i ω) := by
  have h : ∀ᵐ ω ∂P, ∀ i j : ι, i ≠ j → τ i ω ≠ τ j ω := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    by_cases hij : i = j
    · filter_upwards with ω
      intro hne
      exact False.elim (hne hij)
    · filter_upwards [hpair i j hij] with ω hneq
      exact fun _ => hneq
  filter_upwards [h] with ω hω
  intro i j heq
  by_contra hij
  exact (hω i j hij) heq