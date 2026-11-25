-- Prove2me | solution 1 for ErdosPosa.exists_isMax023
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:33:24.529903+00:00
-- url     : https://prove2.me/submissions/c8a65dde-7d10-44d8-817b-7e30929adcc4

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Theorems.Thm_ErdosPosa_dsum_lt_of_lt
public import Theorems.Thm_ErdosPosa_deg_bot
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution [Finite V] (G : SimpleGraph V) : ∃ H, IsMax023 G H := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨H, hH, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => H ≤ G ∧ Deg023 H)
    ).exists_max_image dsum
      ⟨⊥, Finset.mem_filter.2 ⟨Finset.mem_univ _, bot_le, fun v => Or.inl (deg_bot v)⟩⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH hmax
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro K hKG hK hHK u v huv
  by_contra hn
  have := hmax K ⟨hKG, hK⟩
  have := dsum_lt_of_lt hHK huv hn
  omega
end ErdosPosa
