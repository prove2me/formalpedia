-- Prove2me | solution 1 for ErdosRubinTaylor.extend_from_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:38:53.55025+00:00
-- url     : https://prove2.me/submissions/15269eab-a967-4804-ad02-e4b926212b9d

module
public import Mathlib
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Theorems.Thm_ErdosRubinTaylor_dIn_eq
public import Theorems.Thm_ErdosRubinTaylor_greedy_list
public import Theorems.Thm_ErdosRubinTaylor_exists_rank

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
variable [Fintype V]
namespace ErdosRubinTaylor
theorem _root_.solution {C : Type*} [Nonempty C] (G : SimpleGraph V)
    (hconn : G.Connected) (T : Set V) (hTne : T.Nonempty) (hT : DCIn C G T)
    (L : V → Finset C) (hL : ∀ v, dIn G Set.univ v ≤ (L v).card) : ColIn G Set.univ L := by
  classical
  obtain ⟨t0, ht0⟩ := hTne
  have hnear : ∀ v ∈ (Set.univ : Set V), ∃ n, near G Set.univ T n v := by
    intro v _
    have key : ∀ (a b : V) (p : G.Walk a b), b ∈ T → near G Set.univ T p.length a := by
      intro a b p
      induction p with
      | nil => exact id
      | cons h _ ih => exact fun hb => ⟨_, trivial, h, ih hb⟩
    exact ⟨_, key v t0 (hconn.preconnected v t0).some ht0⟩
  obtain ⟨r, hr⟩ := exists_rank G Set.univ T hnear
  obtain ⟨g, hg1, hg2⟩ := greedy_list G L r (univ.filter (· ∉ T)) (by
    intro w hw'
    simp only [mem_filter, mem_univ, true_and] at hw'
    obtain ⟨u0, -, hwu0, hru0⟩ := hr w trivial hw'
    have hsub : univ.filter (fun u => u ∈ univ.filter (· ∉ T) ∧ G.Adj w u ∧ r w ≤ r u) ⊆
        (univ.filter (fun u => u ∈ (Set.univ : Set V) ∧ G.Adj w u)).erase u0 := by
      intro u hu
      simp only [mem_filter, mem_univ, true_and, mem_erase, Set.mem_univ] at hu ⊢
      refine ⟨?_, hu.2.1⟩
      rintro rfl; omega
    have h1 := card_le_card hsub
    have hmem : u0 ∈ univ.filter (fun u => u ∈ (Set.univ : Set V) ∧ G.Adj w u) := by simp [hwu0]
    rw [card_erase_of_mem hmem, ← dIn_eq] at h1
    have hpos : 0 < dIn G Set.univ w := by rw [dIn_eq]; exact card_pos.2 ⟨u0, hmem⟩
    have := hL w
    omega)
  set L' : V → Finset C := fun v =>
    L v \ (univ.filter (fun u => u ∉ T ∧ G.Adj v u)).image g with hL'
  obtain ⟨h, hh1, hh2⟩ := hT L' (by
    intro v hv
    have hsplit : dIn G Set.univ v =
        dIn G T v + (univ.filter (fun u => u ∉ T ∧ G.Adj v u)).card := by
      rw [dIn_eq, dIn_eq, ← card_union_of_disjoint]
      · congr 1; ext u; simp only [mem_filter, mem_univ, true_and, Set.mem_univ, mem_union]
        tauto
      · rw [Finset.disjoint_left]; intro u hu1 hu2
        simp only [mem_filter, mem_univ, true_and] at hu1 hu2; exact hu2.1 hu1.1
    have h1 := le_card_sdiff ((univ.filter (fun u => u ∉ T ∧ G.Adj v u)).image g) (L v)
    have h2 := card_image_le (s := univ.filter (fun u => u ∉ T ∧ G.Adj v u)) (f := g)
    have := hL v
    simp only [hL']
    omega)
  refine ⟨fun v => if v ∈ T then h v else g v, ?_, ?_⟩
  · intro v _
    by_cases hv : v ∈ T
    · simp only [hv, ite_true]; exact (mem_sdiff.1 (hh1 v hv)).1
    · simp only [hv, ite_false]; exact hg1 v (by simpa using hv)
  · intro u _ v _ huv
    by_cases hu : u ∈ T <;> by_cases hv : v ∈ T <;> simp only [hu, hv, ite_true, ite_false]
    · exact hh2 u hu v hv huv
    · intro he
      have := (mem_sdiff.1 (hh1 u hu)).2
      exact this (he ▸ mem_image_of_mem g (by simp [hv, huv]))
    · intro he
      have := (mem_sdiff.1 (hh1 v hv)).2
      exact this (he ▸ mem_image_of_mem g (by simp [hu, huv.symm]))
    · exact hg2 u (by simpa using hu) v (by simpa using hv) huv
end ErdosRubinTaylor
