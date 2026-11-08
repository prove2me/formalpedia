-- Prove2me | solution 1 for CapacityGames.consistent_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:31:40.508022+00:00
-- url     : https://prove2.me/submissions/df16ff46-ef85-46cd-b047-328910a78c9d

import Mathlib
import Definitions.Def_CapacityGames_SetFunction
import Definitions.Def_CapacityGames_Model

open MeasureTheory

open CapacityGames in
theorem solution {N Ω : Type*} [Fintype N] [MeasurableSpace Ω]
    (G : CapacityGame N Ω) (hG : G.IsValid) (Δ : N → (N → ℝ) → ℝ) :
    Consistent G Δ ↔ ∀ S : Finset N,
      (∃ p : Choice N Ω, SCFeasible G p ∧ support p.t ⊆ S ∧
          scProfit G p = scOptValue G S ∧ ∑ j ∈ S, Δ j p.t = 0) ∧
      (∀ p : Choice N Ω, SCFeasible G p → support p.t ⊆ S →
          ∑ j ∈ S, Δ j p.t ≤ scOptValue G S - scProfit G p) := by
  unfold Consistent
  constructor
  · intro h S
    obtain ⟨h1, p, hp1, hp2, hp3, hp4⟩ := h S
    refine ⟨⟨p, hp1, hp2, hp3, by linarith⟩, fun q hq1 hq2 => ?_⟩
    have := h1 q hq1 hq2
    linarith
  · intro h S
    obtain ⟨⟨p, hp1, hp2, hp3, hp4⟩, h1⟩ := h S
    refine ⟨fun q hq1 hq2 => ?_, ⟨p, hp1, hp2, hp3, by linarith⟩⟩
    have := h1 q hq1 hq2
    linarith
