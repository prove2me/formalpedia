-- Prove2me | solution 1 for CliqueMinors.k3_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:43:18.531141+00:00
-- url     : https://prove2.me/submissions/987593f1-da87-4824-84a7-8a6a8b79a485

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_isMinor_of_clique
public import Theorems.Thm_CliqueMinors_isMinor_lift_contract
public import Theorems.Thm_CliqueMinors_contractG_adj
public import Theorems.Thm_CliqueMinors_contract_degree
public import Theorems.Thm_CliqueMinors_contract_support
public import Theorems.Thm_CliqueMinors_mem_merged


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open scoped Classical
variable [Fintype V]
namespace CliqueMinors
theorem _root_.solution : ∀ (n : ℕ) (G : SimpleGraph V) (S : Finset V), S.card = n → S.Nonempty →
    (∀ a b, G.Adj a b → a ∈ S) → (∀ v ∈ S, 2 ≤ G.degree v) →
    IsMinor (⊤ : SimpleGraph (Fin 3)) G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro G S hn hS hsupp hdeg
  obtain ⟨x, hx⟩ := hS
  have hcx : 1 < (G.neighborFinset x).card := by
    rw [card_neighborFinset_eq_degree]; have := hdeg x hx; omega
  obtain ⟨y, hy⟩ := Finset.card_pos.1 (show 0 < (G.neighborFinset x).card by omega)
  rw [mem_neighborFinset] at hy
  by_cases hcom : ∃ z, G.Adj x z ∧ G.Adj y z
  · obtain ⟨z, hxz, hyz⟩ := hcom
    refine isMinor_of_clique ![x, y, z] fun i j h => ?_
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl h |
      simp [hy, hxz, hyz, hy.symm, hxz.symm, hyz.symm]
  simp only [not_exists, not_and] at hcom
  obtain ⟨p, hp, hpy⟩ := Finset.exists_mem_ne hcx y
  rw [mem_neighborFinset] at hp
  have hyS : y ∈ S := hsupp _ _ hy.symm
  have hcy : 1 < (G.neighborFinset y).card := by
    rw [card_neighborFinset_eq_degree]; have := hdeg y hyS; omega
  obtain ⟨q, hq, hqx⟩ := Finset.exists_mem_ne hcy x
  rw [mem_neighborFinset] at hq
  have hpq : p ≠ q := by rintro rfl; exact hcom p hp hq
  refine isMinor_lift_contract (G' := contractG G x y) hy (fun u v h => (contractG_adj.1 h).2)
    (by omega) ?_
  refine ihn _ (hn ▸ Finset.card_erase_lt_of_mem hyS) _ (S.erase y) rfl
    ⟨x, Finset.mem_erase.2 ⟨hy.ne, hx⟩⟩ (contract_support hy hsupp)
    (contract_degree 2 hy hdeg ?_ (fun z hxz hyz => absurd hyz (hcom z hxz)))
  refine Finset.one_lt_card.2 ⟨p, ?_, q, ?_, hpq⟩
  · exact mem_merged.2 ⟨hpy, hp.ne.symm, Or.inl hp⟩
  · exact mem_merged.2 ⟨hq.ne.symm, hqx, Or.inr hq⟩
end CliqueMinors
