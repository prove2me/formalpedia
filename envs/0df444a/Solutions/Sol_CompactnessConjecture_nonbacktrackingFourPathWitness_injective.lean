-- Prove2me | solution 1 for CompactnessConjecture.nonbacktrackingFourPathWitness_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/26032e35-153a-40c3-b434-17e04c0b7d30

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_nonbacktrackingFourPathPair_injective

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} :
    Function.Injective
      (nonbacktrackingFourPathWitness G hbip hfour hsix
        (u := u)) := by
  intro p q hpq
  apply nonbacktrackingFourPathPair_injective G hfour
  exact congrArg Subtype.val hpq
end CompactnessConjecture
