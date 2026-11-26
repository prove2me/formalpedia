-- Prove2me | solution 1 for ErdosRubinTaylor.dIn_clique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:40:38.932115+00:00
-- url     : https://prove2.me/submissions/9c14dd17-895f-4d21-82f7-a8cb770b1288

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai
public import Theorems.Thm_ErdosRubinTaylor_dIn_eq
public import Theorems.Thm_ErdosRubinTaylor_ncard_eq_filter


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V]
namespace ErdosRubinTaylor
theorem _root_.solution {T : Set V} (hK : IsCliqueOn G T) {u : V} (hu : u ∈ T) :
    dIn G T u = T.ncard - 1 := by
  classical
  rw [dIn_eq, ncard_eq_filter]
  have : univ.filter (fun w => w ∈ T ∧ G.Adj u w) = (univ.filter (· ∈ T)).erase u := by
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_erase]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(G.ne_of_adj h2).symm, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, hK u hu w h2 (Ne.symm h1)⟩
  rw [this, card_erase_of_mem (by simpa using hu)]
end ErdosRubinTaylor
