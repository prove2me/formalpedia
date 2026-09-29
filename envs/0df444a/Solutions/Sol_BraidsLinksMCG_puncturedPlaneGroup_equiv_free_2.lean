-- Prove2me | solution 2 for BraidsLinksMCG.puncturedPlaneGroup_equiv_free
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T23:46:50.156163+00:00
-- url     : https://prove2.me/submissions/b73fd123-b44f-415f-bb0f-d8ca10e8b47c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BraidsLinksMCG_puncturedPlaneGroup_free_on_standardGen
import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

theorem _root_.solution (n : ℕ) :
    Nonempty (PuncturedPlaneGroup n ≃* FreeGroup (Fin n)) := by
  obtain ⟨e, _⟩ := BraidsLinksMCG.puncturedPlaneGroup_free_on_standardGen n
  exact ⟨e⟩

#print axioms solution
