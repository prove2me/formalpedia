-- Prove2me | solution 1 for BSLambda.LLL.card_filter_le_of_no_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:08:47.092883+00:00
-- url     : https://prove2.me/submissions/2a784bea-a402-4830-87e4-04c62a38832d

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution {P : ι → Prop} [DecidablePred P] {h : ι} {m : ℕ}
    (hno : ∀ S : Finset ι, S.card = m + 2 → h ∈ S → (∀ i ∈ S, i ≠ h → P i) → False) :
    (Finset.univ.filter fun j => j ≠ h ∧ P j).card ≤ m := by
  by_contra hcontra
  obtain ⟨U, hU, hUcard⟩ := Finset.exists_subset_card_eq (Nat.not_le.mp hcontra)
  have hh : h ∉ U := fun hmem ↦ ((Finset.mem_filter_univ _).mp (hU hmem)).1 rfl
  refine hno (insert h U) ?_ (Finset.mem_insert_self h U) fun i hi hih ↦
    ((Finset.mem_filter_univ _).mp (hU ((Finset.mem_insert.mp hi).resolve_left hih))).2
  rw [Finset.card_insert_of_notMem hh, hUcard]
end BSLambda.LLL
