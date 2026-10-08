-- Prove2me | solution 1 for DoubleGreedyUSM.Deterministic.telescoped
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-05T12:12:08.227138+00:00
-- url     : https://prove2.me/submissions/d6eee900-d867-4a51-81dd-173bf5538548

import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_DoubleGreedyUSM_Deterministic_Algorithm1
import Theorems.Thm_DoubleGreedyUSM_Deterministic_lemma_II_2

open DoubleGreedyUSM.Deterministic

theorem solution {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (O : Finset X)
    (hO : ∀ S, f S ≤ f O) (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l) :
    f (optI O (state f l 0)) - f (optI O (state f l l.length)) ≤
        (f (state f l l.length).1 - f (state f l 0).1) +
          (f (state f l l.length).2 - f (state f l 0).2) ∧
      (f (state f l l.length).1 - f (state f l 0).1) +
          (f (state f l l.length).2 - f (state f l 0).2) ≤
        f (state f l l.length).1 + f (state f l l.length).2 := by
  have ht : ∀ i, i ≤ l.length →
      f (optI O (state f l 0)) - f (optI O (state f l i)) ≤
        (f (state f l i).1 - f (state f l 0).1) +
          (f (state f l i).2 - f (state f l 0).2) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hs := DoubleGreedyUSM.Deterministic.lemma_II_2 f hf O hO l hl hcov
        (i + 1) (by omega) hi
      simp only [Nat.add_sub_cancel] at hs
      linarith
  exact ⟨ht l.length le_rfl, by
    linarith [hf0 (state f l 0).1, hf0 (state f l 0).2]⟩


