-- Prove2me | solution 1 for AvramDividend.Classical.ae_injective_on_active_indices_of_pairwise_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:11:11.899103+00:00
-- url     : https://prove2.me/submissions/8578b64d-d7fa-409b-9650-8f2235847ab2

import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Probability.IdentDistrib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

theorem solution
    {Ω ι α : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) (active : ι → Ω → Prop) (τ : ι → Ω → α)
    (hpair : ∀ i j : ι, i ≠ j →
      ∀ᵐ ω ∂P, active i ω → active j ω → τ i ω ≠ τ j ω) :
    ∀ᵐ ω ∂P, ∀ i j : ι,
      active i ω → active j ω → τ i ω = τ j ω → i = j := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases hij : i = j
  · filter_upwards with ω
    intro _ _ _
    exact hij
  · filter_upwards [hpair i j hij] with ω hω
    intro hi hj htime
    exact False.elim ((hω hi hj) htime)