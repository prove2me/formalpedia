-- Prove2me | solution 1 for BergeMatching.Core.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T15:20:59.075461+00:00
-- url     : https://prove2.me/submissions/949b57ae-c8e5-487e-a48d-5a8425da6d65

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain
import Theorems.Thm_BergeMatching_Core_theorem_1_only_if
import Theorems.Thm_BergeMatching_Core_theorem_1_if

open BergeMatching.Core

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) (hM : M.IsMatching) :
    IsMaximumMatching M ↔
      ¬ ∃ (a a' : V) (p : G.Walk a a'),
          a ≠ a' ∧ IsNeutral M a ∧ IsNeutral M a' ∧ IsAlternatingChain M p := by
  constructor
  · rintro hmax ⟨a, a', p, haa', ha, ha', hp⟩
    obtain ⟨_, -, -, -, hnot⟩ := theorem_1_only_if G M hM p haa' ha ha' hp
    exact hnot hmax
  · intro hno
    by_contra hnot
    exact hno (theorem_1_if G M hM hnot)
