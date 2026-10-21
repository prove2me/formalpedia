-- Prove2me | solution 1 for AvramDividend.Classical.chat03_tendsto_first_passage_of_mesh_brackets
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T21:47:53.403249+00:00
-- url     : https://prove2.me/submissions/ef91a076-ae4a-4010-a1c8-9b6ce22704a8

import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal

/-!
Convert a one-sided epsilon-delta bracket on a vanishing mesh sequence
into genuine convergence of the first-passage approximants.
-/
theorem solution
    (τ : ℝ≥0) (mesh σ : ℕ → ℝ≥0)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)))
    (hbracket : ∀ ε : ℝ≥0, 0 < ε →
      ∃ δ : ℝ≥0, 0 < δ ∧
        ∀ n : ℕ, mesh n < δ →
          τ ≤ σ n ∧ σ n < τ + ε) :
    Tendsto σ atTop (𝓝 τ) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨δ, hδ, hgrid⟩ :=
      hbracket 1 (show (0 : ℝ≥0) < 1 from zero_lt_one)
    have hsmall : ∀ᶠ n in atTop, mesh n < δ :=
      (tendsto_order.1 hzero).2 δ hδ
    filter_upwards [hsmall] with n hn
    exact lt_of_lt_of_le ha (hgrid n hn).1
  · intro a ha
    have hε : 0 < a - τ := tsub_pos_of_lt ha
    obtain ⟨δ, hδ, hgrid⟩ := hbracket (a - τ) hε
    have hsmall : ∀ᶠ n in atTop, mesh n < δ :=
      (tendsto_order.1 hzero).2 δ hδ
    filter_upwards [hsmall] with n hn
    have hlt := (hgrid n hn).2
    simpa [add_tsub_cancel_of_le (le_of_lt ha)] using hlt
