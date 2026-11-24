-- Prove2me | solution 1 for BalanceSpecification.MarkerEmbedding.map_mem_language_renamedShift_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:21.383969+00:00
-- url     : https://prove2.me/submissions/a901e668-1969-47cf-9eff-52ed4f560dc8

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_Specification
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_mem_language_renamedShift_iff

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerEmbedding
variable {A B : Type*}
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace B] [T2Space B]
namespace BalanceSpecification.MarkerEmbedding
theorem _root_.solution {f : A → B} (hf : Function.Injective f)
    {Y : ShiftSpace A} {v : Word A} :
    v.map f ∈ language (renamedShift f Y) ↔ v ∈ language Y := by
  rw [mem_language_renamedShift_iff]
  constructor
  · rintro ⟨u, hu, heq⟩
    have huv : u = v := (List.map_inj_right (fun _ _ h => hf h)).mp heq
    exact huv ▸ hu
  · intro hv
    exact ⟨v, hv, rfl⟩
end BalanceSpecification.MarkerEmbedding
