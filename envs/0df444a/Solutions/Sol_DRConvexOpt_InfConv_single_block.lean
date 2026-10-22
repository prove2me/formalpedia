-- Prove2me | solution 1 for DRConvexOpt.InfConv.single_block
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:12:33.312046+00:00
-- url     : https://prove2.me/submissions/084d96fc-59dc-49e4-b889-f30fbf6097f5

import Mathlib
import Definitions.Def_DRConvexOpt_InfConv_Setting
set_option autoImplicit false
open DRConvexOpt.InfConv
open MeasureTheory Matrix Filter Topology

theorem solution {nP nQ nK nI nJ : ℕ} (d : AmbData nP nQ nK nI)
    (blk : Fin (nI + 1) → Fin nJ) :
    nJ = 1 → ∀ j, outerSet d blk j = ambiguitySet d := by
  intro h
  subst h
  intro j
  ext μ
  simp only [outerSet, ambiguitySet, Set.mem_setOf_eq]
  have : ∀ i, blk i = j := fun i => Subsingleton.elim _ _
  simp [this]
