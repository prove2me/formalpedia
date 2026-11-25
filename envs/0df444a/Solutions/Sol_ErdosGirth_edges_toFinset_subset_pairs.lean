-- Prove2me | solution 1 for ErdosGirth.edges_toFinset_subset_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:30:01.413506+00:00
-- url     : https://prove2.me/submissions/8efa6358-2e9b-4569-9463-53a7ff108e8e

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution {m : ℕ} {u v : Fin m} (c : (⊤ : SimpleGraph (Fin m)).Walk u v) :
    c.edges.toFinset ⊆ pairs m := by
  intro e he
  simp only [pairs, mem_filter, mem_univ, true_and]
  exact (⊤ : SimpleGraph (Fin m)).not_isDiag_of_mem_edgeSet
    (c.edges_subset_edgeSet (List.mem_toFinset.mp he))
end ErdosGirth
