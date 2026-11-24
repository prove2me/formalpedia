-- Prove2me | solution 1 for FFactor.tutte_f_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:17:27.828817+00:00
-- url     : https://prove2.me/submissions/bacfec52-58fb-4130-82a7-39cbc70eb6bc

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorNec
public import Definitions.Def_FFactorLib_FFactorCount
public import Definitions.Def_FFactorLib_FFactor
public import Theorems.Thm_FFactor_exists_factor_of_condition
public import Theorems.Thm_FFactor_gadget_adj_inl_inl
public import Theorems.Thm_FFactor_gadget_adj_inl_inr
public import Theorems.Thm_FFactor_gadget_adj_inr_inl
public import Theorems.Thm_FFactor_gadget_adj_inr_inr
public import Theorems.Thm_FFactor_home_inl
public import Theorems.Thm_FFactor_home_inr
public import Theorems.Thm_FFactor_mem_del_verts
public import Theorems.Thm_FFactor_oddCnt_le_of_factor
attribute [local simp] FFactor.gadget_adj_inl_inl
attribute [local simp] FFactor.gadget_adj_inl_inr
attribute [local simp] FFactor.gadget_adj_inr_inl
attribute [local simp] FFactor.gadget_adj_inr_inr
attribute [local simp] FFactor.home_inl
attribute [local simp] FFactor.home_inr
attribute [local simp] FFactor.mem_del_verts



set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace FFactor
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℕ) :
    (∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, H ≤ G ∧ ∀ v, H.degree v = f v) ↔
      ∀ S T : Finset V, Disjoint S T →
        (oddCount G f S T : ℤ) ≤ ∑ v ∈ S, (f v : ℤ) - ∑ v ∈ T, (f v : ℤ) +
          ∑ v ∈ T, (#{u ∈ G.neighborFinset v | u ∉ S} : ℤ) := by
  have hD : ∀ (H : SimpleGraph V) [DecidableRel H.Adj] v, H.degree v =
      @Finset.card V (@Finset.filter V (fun u => H.Adj v u)
        (fun _ => Classical.propDecidable _) univ) := by
    intro H _ v
    rw [← card_neighborFinset_eq_degree]
    congr 1
    ext u
    simp
  constructor
  · rintro ⟨H, _, hHG, hdeg⟩ S T hST
    have := oddCnt_le_of_factor G H hHG f (fun v => (hD H v).symm.trans (hdeg v)) S T hST
    convert this using 4 with v
    · rfl
    · congr 1
      ext u
      simp
  · intro h
    obtain ⟨H, hHG, hdeg⟩ := exists_factor_of_condition G f (fun S T hST => by
      have := h S T hST
      convert this using 4 with v
      · rfl
      · congr 1
        ext u
        simp)
    classical
    exact ⟨H, inferInstance, hHG, fun v => (hD H v).trans (hdeg v)⟩
end FFactor
