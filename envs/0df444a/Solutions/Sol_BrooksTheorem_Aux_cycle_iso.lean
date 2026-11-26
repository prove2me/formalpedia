-- Prove2me | solution 1 for BrooksTheorem.Aux.cycle_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:46.93779+00:00
-- url     : https://prove2.me/submissions/14a234db-f848-4764-8e33-8b978ec3f6d6

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_Cycle
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
attribute [local simp] BrooksTheorem.Aux.mem_nb



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*} [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution (G : SimpleGraph V) (h2 : ∀ v, (nb G v).card = 2) (n : ℕ)
    (e : Fin (n + 3) ≃ V) (he : ∀ i j, (cycleGraph (n + 3)).Adj i j → G.Adj (e i) (e j)) :
    Nonempty (G ≃g cycleGraph (n + 3)) := by
  classical
  have hconv : ∀ i j, G.Adj (e i) (e j) → (cycleGraph (n + 3)).Adj i j := by
    intro i j hij
    by_contra hnot
    have hc1 : (cycleGraph (n + 3)).Adj i (i - 1) := by
      rw [cycleGraph_adj]; left; simp
    have hc2 : (cycleGraph (n + 3)).Adj i (i + 1) := by
      rw [cycleGraph_adj]; right; simp
    have hpm : i - 1 ≠ i + 1 := by
      intro h
      have := (cycleGraph_degree_three_le (v := i)).symm.trans cycleGraph_degree_two_le
      rw [h] at this
      simp at this
    have hj1 : j ≠ i - 1 := fun h => hnot (h ▸ hc1)
    have hj2 : j ≠ i + 1 := fun h => hnot (h ▸ hc2)
    have hsub : ({e (i - 1), e (i + 1), e j} : Finset V) ⊆ nb G (e i) := by
      intro u hu
      simp only [mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact mem_nb.2 (he _ _ hc1)
      · exact mem_nb.2 (he _ _ hc2)
      · exact mem_nb.2 hij
    have := card_le_card hsub
    rw [h2, card_insert_of_notMem, card_pair] at this
    · omega
    · exact fun h => hj2 (e.injective h).symm
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨fun h => hpm (e.injective h), fun h => hj1 (e.injective h).symm⟩
  refine ⟨⟨e.symm, ?_⟩⟩
  intro a b
  constructor
  · intro h
    have := he _ _ h
    simpa using this
  · intro h
    apply hconv
    simpa using h
end BrooksTheorem.Aux
