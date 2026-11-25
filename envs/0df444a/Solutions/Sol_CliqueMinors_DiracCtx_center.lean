-- Prove2me | solution 1 for CliqueMinors.DiracCtx.center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:45:36.39709+00:00
-- url     : https://prove2.me/submissions/99d51993-a8b2-4dee-9cd3-96c1805bde12

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_DiracCtx_card_nbr
public import Theorems.Thm_CliqueMinors_DiracCtx_contract
public import Theorems.Thm_CliqueMinors_DiracCtx_op
public import Theorems.Thm_CliqueMinors_DiracCtx_deg_four
public import Theorems.Thm_CliqueMinors_eq_of_card_le_three
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
    (hx : ∀ t, G.Adj x t ↔ t = a ∨ t = b ∨ t = c) (hab' : a ≠ b) (hac' : a ≠ c) (hbc' : b ≠ c)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : ¬ G.Adj a c) : False := by
  have hxa : G.Adj x a := (hx a).2 (Or.inl rfl)
  have hxb : G.Adj x b := (hx b).2 (Or.inr (Or.inl rfl))
  have hxc : G.Adj x c := (hx c).2 (Or.inr (Or.inr rfl))
  have hb3 : G.degree b ≤ 3 := by
    by_contra hb4
    obtain ⟨z, hz, hzx, hzb⟩ := exists_mem_ne_ne (H.card_nbr hab) x b
    rw [mem_neighborFinset] at hz
    have hzc : z ≠ c := by rintro rfl; exact hac hz
    refine H.contract hxa (three_le_card (p := b) (q := c) (r := z) ?_ ?_ ?_ hbc' hzb.symm
      hzc.symm) (fun t hxt hat => ?_)
    · exact mem_merged.2 ⟨hab'.symm, hxb.ne.symm, Or.inl hxb⟩
    · exact mem_merged.2 ⟨hac'.symm, hxc.ne.symm, Or.inl hxc⟩
    · exact mem_merged.2 ⟨hz.ne.symm, hzx, Or.inr hz⟩
    · rcases (hx t).1 hxt with rfl | rfl | rfl
      · exact absurd hat (G.loopless.irrefl _)
      · omega
      · exact absurd hat hac
  have hb : ∀ t, G.Adj b t → t = x ∨ t = a ∨ t = c := fun t ht =>
    eq_of_card_le_three (s := G.neighborFinset b) (by rw [card_neighborFinset_eq_degree]; omega)
      (by simpa using hxb.symm) (by simpa using hab.symm) (by simpa using hbc) hxa.ne hxc.ne hac'
      (by simpa using ht)
  have ha4 := H.deg_four hx hb hab hac
  have hc4 := H.deg_four (x := x) (a := c) (b := b) (c := a) (fun t => by rw [hx]; tauto)
    (fun t ht => by rcases hb t ht with h | h | h <;> tauto) hbc.symm (fun h => hac h.symm)
  exact H.op hx hb hab hbc hac hac' ha4 hc4
end CliqueMinors.DiracCtx
