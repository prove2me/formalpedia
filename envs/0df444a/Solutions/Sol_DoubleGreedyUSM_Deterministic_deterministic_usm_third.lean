-- Prove2me | solution 1 for DoubleGreedyUSM.Deterministic.deterministic_usm_third
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-05T12:12:09.859989+00:00
-- url     : https://prove2.me/submissions/e322a41f-47f6-4840-aaa8-e103a0898c35

import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_DoubleGreedyUSM_Deterministic_Algorithm1
import Theorems.Thm_DoubleGreedyUSM_Deterministic_opt_endpoints
import Theorems.Thm_DoubleGreedyUSM_Deterministic_telescoped

open DoubleGreedyUSM.Deterministic

theorem solution {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (l : List X)
    (hl : l.Nodup) (hcov : ∀ x, x ∈ l) :
    (state f l l.length).1 = (state f l l.length).2 ∧
      NonmonotoneSubmod.Shared.OPT f ≤ 3 * f (state f l l.length).1 := by
  classical
  obtain ⟨O, _, hmax⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty :
    (Finset.univ : Finset (Finset X)).Nonempty) f
  have hO : ∀ S, f S ≤ f O := by
    intro S
    rw [← hmax]
    exact Finset.le_sup' f (Finset.mem_univ S)
  obtain ⟨_, hstart, hend, hxy⟩ :=
    DoubleGreedyUSM.Deterministic.opt_endpoints f O hO l hl hcov
  have ht := DoubleGreedyUSM.Deterministic.telescoped f hf0 hf O hO l hl hcov
  have hb := ht.1.trans ht.2
  rw [hstart, hend, ← hxy] at hb
  refine ⟨hxy, ?_⟩
  change NonmonotoneSubmod.Shared.OPT f = f O at hmax
  rw [hmax]
  linarith


