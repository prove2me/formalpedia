-- Prove2me | solution 1 for ErdosRubinTaylor.exists_third
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:41:00.81393+00:00
-- url     : https://prove2.me/submissions/618073f4-f617-4a1f-80b3-a3af00d161ef

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_BrooksLib_Brooks
public import Definitions.Def_ChoosabilityLib_ERTChoosable
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
public import Theorems.Thm_BrooksTheorem_Aux_restr_adj
attribute [local simp] BrooksTheorem.Aux.mem_nb
attribute [local simp] BrooksTheorem.Aux.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
namespace ErdosRubinTaylor
theorem _root_.solution {S : Set V} (h3 : 3 ≤ S.ncard) (a b : V) : ∃ x ∈ S, x ≠ a ∧ x ≠ b := by
  by_contra h
  push Not at h
  have hsub : S ⊆ {a, b} := fun x hx => by
    by_cases hxa : x = a
    · simp [hxa]
    · simp [h x hx hxa]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_insert_le a ({b} : Set V)
  rw [Set.ncard_singleton] at h2
  omega
end ErdosRubinTaylor
