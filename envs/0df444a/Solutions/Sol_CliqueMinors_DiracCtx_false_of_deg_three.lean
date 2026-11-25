-- Prove2me | solution 1 for CliqueMinors.DiracCtx.false_of_deg_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:46:52.664722+00:00
-- url     : https://prove2.me/submissions/2ec07bca-40fc-4b38-9d0e-34d730c335e2

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_isMinor_K4_of_clique
public import Theorems.Thm_CliqueMinors_DiracCtx_step_nbr
public import Theorems.Thm_CliqueMinors_DiracCtx_center

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
theorem _root_.solution (H : DiracCtx G S) {x : V} (hx3 : G.degree x = 3) : False := by
  obtain ⟨a, b, c, hab, hac, hbc, hN⟩ := Finset.card_eq_three.1
    ((card_neighborFinset_eq_degree G x).trans hx3)
  have hx : ∀ t, G.Adj x t ↔ t = a ∨ t = b ∨ t = c := fun t => by
    rw [← mem_neighborFinset, hN]; simp
  have hxa : G.Adj x a := (hx a).2 (Or.inl rfl)
  have hxb : G.Adj x b := (hx b).2 (Or.inr (Or.inl rfl))
  have hxc : G.Adj x c := (hx c).2 (Or.inr (Or.inr rfl))
  have ha := H.step_nbr hx hab hac hbc
  have hb := H.step_nbr (x := x) (a := b) (b := a) (c := c) (fun t => by rw [hx]; tauto)
    hab.symm hbc hac
  have hc := H.step_nbr (x := x) (a := c) (b := a) (c := b) (fun t => by rw [hx]; tauto)
    hac.symm hbc.symm hab
  by_cases h1 : G.Adj a b <;> by_cases h2 : G.Adj a c <;> by_cases h3 : G.Adj b c
  · exact H.notK4 (isMinor_K4_of_clique hxa hxb hxc h1 h2 h3)
  · exact H.center (x := x) (a := b) (b := a) (c := c) (fun t => by rw [hx]; tauto) hab.symm hbc
      hac h1.symm h2 h3
  · exact H.center hx hab hac hbc h1 h3 h2
  · exact absurd (hc.resolve_left (fun h => h2 h.symm)) (fun h => h3 h.symm)
  · exact H.center (x := x) (a := b) (b := c) (c := a) (fun t => by rw [hx]; tauto) hbc
      hab.symm hac.symm h3 h2.symm (fun h => h1 h.symm)
  · exact absurd (hb.resolve_left (fun h => h1 h.symm)) h3
  · exact absurd (ha.resolve_left h1) h2
  · exact absurd (ha.resolve_left h1) h2
end CliqueMinors.DiracCtx
