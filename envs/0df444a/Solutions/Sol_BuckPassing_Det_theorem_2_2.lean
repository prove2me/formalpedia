-- Prove2me | solution 2 for BuckPassing.Det.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T16:32:11.827302+00:00
-- url     : https://prove2.me/submissions/088375a4-8c8e-400d-a2fd-f1e75e637801

import Mathlib
import Definitions.Def_BuckPassing_Det_Model
import Theorems.Thm_BuckPassing_Det_theorem_1

set_option autoImplicit false
open BuckPassing.Det

-- carved from submission 2347c8e2-b121-4fb2-8b14-4ae975d65e76, lines 584-595

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : BPGraph V) :
    ∃ s : ∀ i, Strat G i, IsPFNE G s := by
  haveI : ∀ i, Nonempty (Strat G i) := fun i => by
    obtain ⟨j, hj⟩ := G.outNonempty i
    exact ⟨⟨j, hj⟩⟩
  haveI : ∀ i, Finite (Strat G i) := fun i => by
    unfold Strat; infer_instance
  obtain ⟨s, hs⟩ := Finite.exists_min (Psi G)
  refine ⟨s, fun mu hmu i x hlt => ?_⟩
  exact absurd (BuckPassing.Det.theorem_1 G mu hmu s i x hlt) (not_lt.mpr (hs _))
