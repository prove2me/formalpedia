-- Prove2me | solution 1 for FairSelling.biU_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:53.076368+00:00
-- url     : https://prove2.me/submissions/2cd02669-b7ba-45ee-94dd-9f0dce129540

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (A : Fin 2 → Finset G) : Finset.univ.biUnion A = A 0 ∪ A 1 := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union, Fin.exists_fin_two]
end FairSelling
