-- Prove2me | solution 1 for CompactnessConjecture.proposedFamilyFree_edge_has_gammaBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/8b0ca610-4b53-4e20-9a55-884f40c1e71e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamilyFree_not_adj_gammaGood
import Theorems.Thm_CompactnessConjecture_mem_gammaBadVertices

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    {u v : Fin n}
    (hedge : host.Adj u v) :
    u ∈ gammaBadVertices host ∨ v ∈ gammaBadVertices host := by
  classical
  by_cases hu : GammaGood host u
  · right
    apply (mem_gammaBadVertices host v).mpr
    intro hv
    exact proposedFamilyFree_not_adj_gammaGood
      host hfree hbip hu hv hedge
  · left
    exact (mem_gammaBadVertices host u).mpr hu
end CompactnessConjecture
