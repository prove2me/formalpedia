-- Prove2me | solution 1 for CompactnessConjecture.booleanCut_flip_neighborFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/40d3cae7-f214-4bca-9cae-b4d5c4b3d468

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace CompactnessConjecture
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (v : V) :
    (booleanCut G (flipBooleanColor color v)).neighborFinset v =
      G.neighborFinset v \ (booleanCut G color).neighborFinset v := by
  classical
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff,
    booleanCut_adj]
  by_cases hwv : w = v
  · subst w
    simp
  · cases hcv : color v <;> cases hcw : color w <;>
      simp [flipBooleanColor, hwv, hcv, hcw]
end CompactnessConjecture
