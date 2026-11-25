-- Prove2me | solution 1 for DiracCycle.exists_cycArr_through
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:58:51.80533+00:00
-- url     : https://prove2.me/submissions/4b87c554-45ef-4461-9c2c-f090d83bf827

module
public import Mathlib
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_DiracCycleLib_DiracCycle
public import Theorems.Thm_DiracCycle_extend_through
public import Theorems.Thm_Hamiltonicity_CycArr_eq_mod
public import Theorems.Thm_Hamiltonicity_CycArr_pos
public import Theorems.Thm_Hamiltonicity_CycArr_rotate
public import Theorems.Thm_Hamiltonicity_exists_cycArr_of_conn


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open DiracCycle
open Hamiltonicity
variable {V : Type*} {G : SimpleGraph V}
namespace DiracCycle
theorem _root_.solution [Fintype V] {k : ℕ} (hk : 2 ≤ k) (hn : k < Fintype.card V)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) (T : Finset V)
    (hT : #T ≤ k) : ∃ m f, CycArr G m f ∧ ∀ y ∈ T, ∃ i, f i = y := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    obtain ⟨m, f, h⟩ := exists_cycArr_of_conn (by omega) hk hconn
    exact ⟨m, f, h, by simp⟩
  | insert x T hxT ih =>
    rw [Finset.card_insert_of_notMem hxT] at hT
    obtain ⟨m, f, hC, hTC⟩ := ih (by omega)
    by_cases hxC : ∃ i, f i = x
    · refine ⟨m, f, hC, ?_⟩
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hxC
      · exact hTC y hy
    push Not at hxC
    -- rotate so that `f 0 ∈ T` when `T` is nonempty
    obtain ⟨f', hC', hTC', hx', hT0⟩ : ∃ f', CycArr G m f' ∧ (∀ y ∈ T, ∃ i, f' i = y) ∧
        (∀ i, f' i ≠ x) ∧ (T.Nonempty → f' 0 ∈ T) := by
      by_cases hTne : T.Nonempty
      · obtain ⟨y, hy⟩ := hTne
        obtain ⟨i, hi⟩ := hTC y hy
        refine ⟨fun j => f (i + j), hC.rotate i, ?_, fun j => hxC _, fun _ => by
          simp only [Nat.add_zero]; rw [hi]; exact hy⟩
        intro y' hy'
        obtain ⟨i', hi'⟩ := hTC y' hy'
        refine ⟨i' + m * i - i, ?_⟩
        have hm0 := hC.pos
        have : i ≤ i' + m * i := le_add_left (Nat.le_mul_of_pos_left i hm0)
        simp only
        rw [Nat.add_sub_cancel' this, hC.eq_mod, Nat.add_mul_mod_self_left, ← hC.eq_mod, hi']
      · exact ⟨f, hC, hTC, hxC, fun h => absurd h hTne⟩
    obtain ⟨m', g, hg, hgx, hgT⟩ := extend_through hk hconn hC' T (by omega) hT0 hx'
    refine ⟨m', g, hg, ?_⟩
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hgx
    · obtain ⟨i, rfl⟩ := hTC' y hy
      rw [hC'.eq_mod i]
      exact hgT _ (Nat.mod_lt _ hC'.pos) (by rw [← hC'.eq_mod]; exact hy)
end DiracCycle
