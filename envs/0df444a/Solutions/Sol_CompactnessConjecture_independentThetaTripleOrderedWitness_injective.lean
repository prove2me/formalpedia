-- Prove2me | solution 1 for CompactnessConjecture.independentThetaTripleOrderedWitness_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/f1fe7dae-5038-48f1-a060-514d5a38d312

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    Function.Injective
      (independentThetaTripleOrderedWitness G hbip hfour hsix) := by
  intro left right heq
  have hbase : independentThetaTripleBase G left =
      independentThetaTripleBase G right := by
    funext index
    fin_cases index
    · exact congrArg (fun witness : OrderedThetaWitness G => witness.2.2.1) heq
    · exact congrArg (fun witness : OrderedThetaWitness G => witness.1) heq
    · exact congrArg (fun witness : OrderedThetaWitness G => witness.2.1) heq
  apply Subtype.ext
  ext vertex
  constructor
  · intro hvertex
    obtain ⟨index, rfl⟩ := independentThetaTripleBase_surjective G left hvertex
    rw [hbase]
    exact independentThetaTripleBase_mem G right index
  · intro hvertex
    obtain ⟨index, rfl⟩ := independentThetaTripleBase_surjective G right hvertex
    rw [← hbase]
    exact independentThetaTripleBase_mem G left index
end CompactnessConjecture
