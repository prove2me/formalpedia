-- Prove2me | solution 1 for ChvatalPosa.chvatal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:34:54.129209+00:00
-- url     : https://prove2.me/submissions/7cc361ed-39d5-46e3-91bb-0628ec974932

module
public import Mathlib
public import Definitions.Def_MengerHamilton_Hamiltonian
public import Definitions.Def_ChvatalPosaLib_ChvatalPosa
public import Theorems.Thm_ChvatalPosa_chvatalCond_mono
public import Theorems.Thm_ChvatalPosa_exists_nonadj_degree_sum
public import Theorems.Thm_Hamiltonicity_isHamiltonian_of_forall_adj
public import Theorems.Thm_Hamiltonicity_isHamiltonian_sup_edge_iff


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ChvatalPosa
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace ChvatalPosa
theorem _root_.solution (hn : 3 ≤ Fintype.card V)
    (h : ∀ i : ℕ, 1 ≤ i → 2 * i < Fintype.card V →
      i ≤ #{v | G.degree v ≤ i} → i + 1 ≤ #{v | Fintype.card V - i ≤ G.degree v}) :
    G.IsHamiltonian := by
  suffices key : ∀ N (H : SimpleGraph V) [DecidableRel H.Adj],
      #{p : V × V | p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2} = N → ChvatalCond H → H.IsHamiltonian from
    key _ G rfl h
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro H _ hN hH
  by_cases hall : ∀ u v, u ≠ v → H.Adj u v
  · exact Hamiltonicity.isHamiltonian_of_forall_adj hn hall
  push Not at hall
  obtain ⟨u, v, huv, hnadj, hdeg⟩ := exists_nonadj_degree_sum H hn hH hall
  classical
  have hle : H ≤ H ⊔ edge u v := le_sup_left
  rw [← Hamiltonicity.isHamiltonian_sup_edge_iff H huv hnadj hdeg]
  refine ih _ ?_ (H ⊔ edge u v) rfl (chvatalCond_mono hle hH)
  rw [← hN]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(u, v), ?_, ?_⟩
    · simp [huv, hnadj]
    · simp [huv, edge_adj]
  · intro p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 (hle h)⟩
end ChvatalPosa
