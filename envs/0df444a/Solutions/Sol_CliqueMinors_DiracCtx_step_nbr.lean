-- Prove2me | solution 1 for CliqueMinors.DiracCtx.step_nbr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:22.734549+00:00
-- url     : https://prove2.me/submissions/df2cbc56-051f-451f-9a11-3db5acf411f6

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_DiracCtx_card_nbr
public import Theorems.Thm_CliqueMinors_DiracCtx_contract
public import Theorems.Thm_CliqueMinors_exists_mem_ne_ne
public import Theorems.Thm_CliqueMinors_mem_merged
public import Theorems.Thm_CliqueMinors_three_le_card


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open scoped Classical
variable [Fintype V]
open CliqueMinors.DiracCtx
variable {G : SimpleGraph V} {S : Finset V}
namespace CliqueMinors.DiracCtx
theorem _root_.solution (H : DiracCtx G S) {x a b c : V}
    (hx : ∀ t, G.Adj x t ↔ t = a ∨ t = b ∨ t = c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.Adj a b ∨ G.Adj a c := by
  by_contra hn
  simp only [not_or] at hn
  have hxa : G.Adj x a := (hx a).2 (Or.inl rfl)
  have hxb : G.Adj x b := (hx b).2 (Or.inr (Or.inl rfl))
  have hxc : G.Adj x c := (hx c).2 (Or.inr (Or.inr rfl))
  obtain ⟨z, hz, hzx, -⟩ := exists_mem_ne_ne (H.card_nbr hxa.symm) x x
  rw [mem_neighborFinset] at hz
  have hzb : z ≠ b := by rintro rfl; exact hn.1 hz
  have hzc : z ≠ c := by rintro rfl; exact hn.2 hz
  refine H.contract hxa (three_le_card (p := b) (q := c) (r := z) ?_ ?_ ?_ hbc hzb.symm hzc.symm)
    (fun t hxt hat => ?_)
  · exact mem_merged.2 ⟨hab.symm, hxb.ne.symm, Or.inl hxb⟩
  · exact mem_merged.2 ⟨hac.symm, hxc.ne.symm, Or.inl hxc⟩
  · exact mem_merged.2 ⟨hz.ne.symm, hzx, Or.inr hz⟩
  · rcases (hx t).1 hxt with rfl | rfl | rfl
    · exact absurd hat (G.loopless.irrefl _)
    · exact absurd hat hn.1
    · exact absurd hat hn.2
end CliqueMinors.DiracCtx
