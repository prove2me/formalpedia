-- Prove2me | solution 1 for ErdosRubinTaylor.cut_decomp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:41:19.394547+00:00
-- url     : https://prove2.me/submissions/d47f40eb-cca2-45fc-b847-cb3cb68fa5f3

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai
public import Theorems.Thm_ErdosRubinTaylor_reach_cut
public import Theorems.Thm_ErdosRubinTaylor_sconn_insert
public import Theorems.Thm_ErdosRubinTaylor_rtg_mem
public import Theorems.Thm_ErdosRubinTaylor_sconn_of_hub


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}
namespace ErdosRubinTaylor
theorem _root_.solution {T : Set V} (hT : SConn G T) {x : V} (hx : x ∈ T)
    (hcut : ¬ SConn G (T \ {x})) (hne : (T \ {x}).Nonempty) :
    ∃ A B : Set V, A ∪ B = T \ {x} ∧ Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) ∧ SConn G (insert x A) ∧ SConn G (insert x B) := by
  obtain ⟨a, ha⟩ := hne
  set W := T \ {x} with hW
  set A : Set V := {v | Relation.ReflTransGen (adjIn G W) a v} with hA
  have hAW : A ⊆ W := fun v hv => rtg_mem hv ha
  have hclA : ∀ u ∈ A, ∀ v ∈ W, G.Adj u v → v ∈ A :=
    fun u hu v hv huv => Relation.ReflTransGen.tail hu ⟨hAW hu, hv, huv⟩
  have hclB : ∀ u ∈ W \ A, ∀ v ∈ W, G.Adj u v → v ∈ W \ A := by
    intro u hu v hv huv
    refine ⟨hv, fun hvA => hu.2 ?_⟩
    exact hclA v hvA u hu.1 huv.symm
  have hreach := fun v (hv : v ∈ W) => reach_cut hT hx hv
  refine ⟨A, W \ A, Set.union_sdiff_cancel hAW, Set.disjoint_sdiff_right, ⟨a, .refl⟩, ?_, ?_,
    sconn_insert hAW hclA hreach, sconn_insert Set.sdiff_subset hclB hreach⟩
  · by_contra hB
    apply hcut
    refine sconn_of_hub ha fun v hv => ?_
    by_contra hva
    exact hB ⟨v, hv, hva⟩
  · intro u hu v hv huv
    exact hv.2 (hclA u hu v hv.1 huv)
end ErdosRubinTaylor
