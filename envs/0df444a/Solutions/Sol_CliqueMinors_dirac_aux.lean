-- Prove2me | solution 1 for CliqueMinors.dirac_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:48:37.443891+00:00
-- url     : https://prove2.me/submissions/2d72d7ff-c981-4e01-b655-14c494c51962

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_isMinor_mono
public import Theorems.Thm_P2M_CliqueMinors_DiracCtx_deg__09077c9cb2b4
public import Theorems.Thm_CliqueMinors_DiracCtx_false_of_deg_three
public import Theorems.Thm_CliqueMinors_exists_mem_ne_ne


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
    (∀ a b, G.Adj a b → a ∈ S) → (∀ v ∈ S, 3 ≤ G.degree v) →
    IsMinor (⊤ : SimpleGraph (Fin 4)) G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro G S hn hS hsupp hdeg
  suffices ∀ m (G : SimpleGraph V), G.edgeFinset.card = m → (∀ a b, G.Adj a b → a ∈ S) →
      (∀ v ∈ S, 3 ≤ G.degree v) → IsMinor (⊤ : SimpleGraph (Fin 4)) G from
    this _ G rfl hsupp hdeg
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro G hm hsupp hdeg
  by_contra hK
  have H : DiracCtx G S := ⟨hsupp, hdeg, hK, fun G' S' hS' hne hsupp' hdeg' =>
    ihn S'.card (hn ▸ hS') G' S' rfl hne hsupp' hdeg'⟩
  have hM1 : ∀ u v, G.Adj u v → 4 ≤ G.degree u → 4 ≤ G.degree v → False := by
    intro u v huv hu hv
    apply hK
    refine isMinor_mono (G.deleteEdges_le {s(u, v)}) ?_
    refine ihm _ ?_ (G.deleteEdges {s(u, v)}) rfl
      (fun a b h => hsupp a b (deleteEdges_le _ h)) (fun w hw => ?_)
    · rw [← hm]
      refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun e he => ?_).2
        ⟨s(u, v), by simpa using huv, by simp [mem_edgeFinset, edgeSet_deleteEdges]⟩)
      simp only [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff] at he ⊢
      exact he.1
    · rw [← card_neighborFinset_eq_degree]
      by_cases hwu : w = u
      · subst hwu
        refine le_trans ?_ (Finset.card_le_card (s := (G.neighborFinset w).erase v) ?_)
        · rw [Finset.card_erase_of_mem (by simpa using huv), card_neighborFinset_eq_degree]
          omega
        · intro t ht
          simp only [Finset.mem_erase, mem_neighborFinset] at ht
          rw [mem_neighborFinset, deleteEdges_adj]
          refine ⟨ht.2, ?_⟩
          simp only [Set.mem_singleton_iff, Sym2.congr_right]
          exact ht.1
      by_cases hwv : w = v
      · subst hwv
        refine le_trans ?_ (Finset.card_le_card (s := (G.neighborFinset w).erase u) ?_)
        · rw [Finset.card_erase_of_mem (by simpa using huv.symm), card_neighborFinset_eq_degree]
          omega
        · intro t ht
          simp only [Finset.mem_erase, mem_neighborFinset] at ht
          rw [mem_neighborFinset, deleteEdges_adj]
          refine ⟨ht.2, ?_⟩
          simp only [Set.mem_singleton_iff, Sym2.eq_swap (a := u), Sym2.congr_right]
          exact ht.1
      · refine le_trans ?_ (Finset.card_le_card (s := G.neighborFinset w) ?_)
        · rw [card_neighborFinset_eq_degree]; exact hdeg w hw
        · intro t ht
          rw [mem_neighborFinset] at ht
          rw [mem_neighborFinset, deleteEdges_adj]
          refine ⟨ht, ?_⟩
          simp only [Set.mem_singleton_iff, Sym2.eq_iff]
          tauto
  obtain ⟨v, hv⟩ := hS
  obtain ⟨u, hu, -⟩ := exists_mem_ne_ne (s := G.neighborFinset v)
    (by rw [card_neighborFinset_eq_degree]; exact hdeg v hv) v v
  rw [mem_neighborFinset] at hu
  by_cases hv3 : G.degree v = 3
  · exact H.false_of_deg_three hv3
  by_cases hu3 : G.degree u = 3
  · exact H.false_of_deg_three hu3
  have := hdeg v hv
  have := H.deg' hu.symm
  exact hM1 v u hu (by omega) (by omega)
end CliqueMinors
