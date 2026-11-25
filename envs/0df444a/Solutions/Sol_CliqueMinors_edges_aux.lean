-- Prove2me | solution 1 for CliqueMinors.edges_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:55.132734+00:00
-- url     : https://prove2.me/submissions/210b3ccf-f944-4c80-8141-122cf47504a9

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_isMinor_mono
public import Theorems.Thm_CliqueMinors_exists_low_deg_K4
public import Theorems.Thm_CliqueMinors_card_edges_deleteIncidenceSet
public import Theorems.Thm_CliqueMinors_deleteIncidenceSet_supp
public import Theorems.Thm_P2M_CliqueMinors_deleteIncidenceSet_le__01daa08c1827


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open scoped Classical
variable [Fintype V]
namespace CliqueMinors
theorem _root_.solution : ∀ (n : ℕ) (G : SimpleGraph V) (S : Finset V), S.card = n → 2 ≤ n →
    (∀ a b, G.Adj a b → a ∈ S) → ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G →
    G.edgeFinset.card + 3 ≤ 2 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro G S hn h2 hsupp hK
  obtain ⟨v, hv, hdv⟩ := exists_low_deg_K4 G S (Finset.card_pos.1 (by omega)) hsupp hK
  obtain ⟨G', hG'⟩ : ∃ G', G' = G.deleteIncidenceSet v := ⟨_, rfl⟩
  have hE := card_edges_deleteIncidenceSet G G' v hG'
  have hK' : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G' :=
    fun h => hK (isMinor_mono (hG' ▸ deleteIncidenceSet_le' G v) h)
  have hsupp' : ∀ a b, G'.Adj a b → a ∈ S.erase v := by
    subst hG'; exact deleteIncidenceSet_supp hsupp
  have hcard : (S.erase v).card = n - 1 := by rw [Finset.card_erase_of_mem hv, hn]
  by_cases hn2 : n = 2
  · subst hn2
    have hE0 : G'.edgeFinset.card = 0 := by
      refine Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun e he => ?_)
      induction e using Sym2.ind with
      | _ a b =>
        have hab : G'.Adj a b := by simpa using he
        have ha := hsupp' a b hab
        have hb := hsupp' b a hab.symm
        exact hab.ne (Finset.card_le_one.1 (by omega) a ha b hb)
    have hdeg1 : G.degree v ≤ 1 := by
      rw [← card_neighborFinset_eq_degree]
      refine (Finset.card_le_card fun t ht => ?_).trans hcard.le
      rw [mem_neighborFinset] at ht
      exact Finset.mem_erase.2 ⟨ht.ne.symm, hsupp _ _ ht.symm⟩
    omega
  · have := ihn (n - 1) (by omega) G' (S.erase v) hcard (by omega) hsupp' hK'
    omega
end CliqueMinors
