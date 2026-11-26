-- Prove2me | solution 1 for ErdosRubinTaylor.sconn_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:39:47.680014+00:00
-- url     : https://prove2.me/submissions/c4fc542d-d91a-4b2b-bce3-8e2f78eaae38

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai
public import Theorems.Thm_ErdosRubinTaylor_rtg_closed
public import Theorems.Thm_ErdosRubinTaylor_rtg_mono
public import Theorems.Thm_ErdosRubinTaylor_rtg_symm
public import Theorems.Thm_ErdosRubinTaylor_sconn_of_hub


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}
namespace ErdosRubinTaylor
theorem _root_.solution {W D : Set V} {x : V} (hDW : D ⊆ W)
    (hcl : ∀ u ∈ D, ∀ v ∈ W, G.Adj u v → v ∈ D)
    (hreach : ∀ v ∈ W, ∃ c ∈ W, G.Adj c x ∧ Relation.ReflTransGen (adjIn G W) v c) :
    SConn G (insert x D) := by
  refine sconn_of_hub (Set.mem_insert x D) fun v hv => ?_
  rcases hv with rfl | hv
  · exact .refl
  · obtain ⟨c, -, hcx, hvc⟩ := hreach v (hDW hv)
    obtain ⟨h1, h2⟩ := rtg_closed hcl hvc hv
    refine rtg_symm ((rtg_mono (Set.subset_insert x D) h1).tail ?_)
    exact ⟨Set.mem_insert_of_mem _ h2, Set.mem_insert _ _, hcx⟩
end ErdosRubinTaylor
