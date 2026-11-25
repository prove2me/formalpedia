-- Prove2me | solution 1 for CliqueMinors.DiracCtx.deg_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:23.745938+00:00
-- url     : https://prove2.me/submissions/2b791e0e-4a69-4cd1-b26d-cdcf9fa609ad

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_DiracCtx_card_nbr
public import Theorems.Thm_CliqueMinors_DiracCtx_contract
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
    (hx : ∀ t, G.Adj x t ↔ t = a ∨ t = b ∨ t = c)
    (hb : ∀ t, G.Adj b t → t = x ∨ t = a ∨ t = c)
    (hab : G.Adj a b) (hac : ¬ G.Adj a c) : 4 ≤ G.degree a := by
  by_contra hlt
  have hxa : G.Adj x a := (hx a).2 (Or.inl rfl)
  have hxb : G.Adj x b := (hx b).2 (Or.inr (Or.inl rfl))
  obtain ⟨z, hz, hzx, hzb⟩ := exists_mem_ne_ne (H.card_nbr hab) x b
  rw [mem_neighborFinset] at hz
  have hzc : z ≠ c := by rintro rfl; exact hac hz
  have hNa : ∀ t, G.Adj a t → t = x ∨ t = b ∨ t = z := fun t ht =>
    eq_of_card_le_three (s := G.neighborFinset a)
      (by rw [card_neighborFinset_eq_degree]; omega) (by simpa using hxa.symm) (by simpa using hab)
      (by simpa using hz) hxb.ne hzx.symm hzb.symm (by simpa using ht)
  have hzx' : ¬ G.Adj z x := fun h => by
    rcases (hx z).1 h.symm with rfl | rfl | rfl
    · exact G.loopless.irrefl _ hz
    · exact hzb rfl
    · exact hzc rfl
  have hzb' : ¬ G.Adj z b := fun h => by
    rcases hb z h.symm with rfl | rfl | rfl
    · exact hzx rfl
    · exact G.loopless.irrefl _ hz
    · exact hzc rfl
  obtain ⟨w, hw, hwa, -⟩ := exists_mem_ne_ne (H.card_nbr hz.symm) a a
  rw [mem_neighborFinset] at hw
  have hwx : w ≠ x := by rintro rfl; exact hzx' hw
  have hwb : w ≠ b := by rintro rfl; exact hzb' hw
  refine H.contract hz (three_le_card (p := x) (q := b) (r := w) ?_ ?_ ?_ hxb.ne hwx.symm
    hwb.symm) (fun t hat hzt => ?_)
  · exact mem_merged.2 ⟨hzx.symm, hxa.ne, Or.inl hxa.symm⟩
  · exact mem_merged.2 ⟨hzb.symm, hab.ne.symm, Or.inl hab⟩
  · exact mem_merged.2 ⟨hw.ne.symm, hwa, Or.inr hw⟩
  · rcases hNa t hat with rfl | rfl | rfl
    · exact absurd hzt hzx'
    · exact absurd hzt hzb'
    · exact absurd hzt (G.loopless.irrefl _)
end CliqueMinors.DiracCtx
