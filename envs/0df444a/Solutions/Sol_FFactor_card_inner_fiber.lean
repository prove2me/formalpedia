-- Prove2me | solution 1 for FFactor.card_inner_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:01:05.071255+00:00
-- url     : https://prove2.me/submissions/f3056f3b-cbf4-42cf-89e9-09157cd69c54

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorSuff
public import Definitions.Def_FFactorLib_FFactorCount
public import Theorems.Thm_FFactor_gadget_adj_inl_inl
public import Theorems.Thm_FFactor_gadget_adj_inl_inr
public import Theorems.Thm_FFactor_gadget_adj_inr_inl
public import Theorems.Thm_FFactor_gadget_adj_inr_inr
public import Theorems.Thm_FFactor_home_inl
public import Theorems.Thm_FFactor_home_inr
public import Theorems.Thm_FFactor_mem_del_verts
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
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : V → ℕ}
  {U : Set (GV G f)}
namespace FFactor
theorem _root_.solution (r : V) :
    #{p : Σ v : V, Fin (G.degree v - f v) | p.1 = r} = G.degree r - f r := by
  have : #(univ : Finset (Fin (G.degree r - f r))) =
      #{p : Σ v : V, Fin (G.degree v - f v) | p.1 = r} := by
    apply card_bij (fun (i : Fin (G.degree r - f r)) _ =>
      (⟨r, i⟩ : Σ v : V, Fin (G.degree v - f v)))
    · intro i _; simp
    · intro i _ j _ h; exact eq_of_heq (Sigma.mk.inj h).2
    · rintro ⟨r', j⟩ h
      simp only [mem_filter, mem_univ, true_and] at h
      subst h
      exact ⟨j, mem_univ _, rfl⟩
  rw [← this, card_univ, Fintype.card_fin]
end FFactor
