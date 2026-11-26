-- Prove2me | solution 1 for BrooksTheorem.Aux.mu_addE_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:36:23.7368+00:00
-- url     : https://prove2.me/submissions/5242883b-93dd-4114-a8ab-82cc3ccdf678

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
public import Theorems.Thm_BrooksTheorem_Aux_restr_adj
public import Theorems.Thm_BrooksTheorem_Aux_addE_adj
public import Theorems.Thm_BrooksTheorem_Aux_mem_pairs
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
attribute [local simp] BrooksTheorem.Aux.mem_nb


attribute [local simp] BrooksTheorem.Aux.restr_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution (H : SimpleGraph V) (S : Set V) {x z px pz : V} (hxz : x ≠ z) (hzS : z ∈ S)
    (hpx : H.Adj x px) (hpxS : px ∉ S) (hpz : H.Adj z pz) (hpzS : pz ∉ S) :
    mu (restr H S ⊔ edge x z) < mu H := by
  classical
  have h1 : pairs (restr H S ⊔ edge x z) ⊆ pairs (restr H S) ∪ {(x, z), (z, x)} := by
    intro p hp
    rw [mem_pairs, addE_adj] at hp
    rcases hp with hp | ⟨hp, _⟩
    · exact mem_union_left _ (mem_pairs.2 hp)
    · apply mem_union_right
      rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [Prod.ext_iff, h1, h2]
      · simp [Prod.ext_iff, h1, h2]
  have h2 : (pairs (restr H S) ∪ {(x, z), (z, x)}).card ≤ mu (restr H S) + 2 := by
    refine (card_union_le _ _).trans ?_
    unfold mu
    have := card_insert_le (x, z) {(z, x)}
    simp only [card_singleton] at this
    omega
  have hD : Disjoint (pairs (restr H S)) {(x, px), (px, x), (z, pz)} := by
    rw [Finset.disjoint_left]
    intro p hp hpD
    rw [mem_pairs] at hp
    simp only [mem_insert, mem_singleton] at hpD
    rcases hpD with rfl | rfl | rfl
    · exact hpxS hp.2.2
    · exact hpxS hp.2.1
    · exact hpzS hp.2.2
  have hcard3 : ({(x, px), (px, x), (z, pz)} : Finset (V × V)).card = 3 := by
    have hxpx : x ≠ px := H.ne_of_adj hpx
    have hpxz : px ≠ z := fun h => hpxS (h ▸ hzS)
    rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simp [Prod.ext_iff, hpxz]
    · simp [Prod.ext_iff, hxpx, hxz]
  have h3 : pairs (restr H S) ∪ {(x, px), (px, x), (z, pz)} ⊆ pairs H := by
    intro p hp
    rcases mem_union.1 hp with hp | hp
    · exact mem_pairs.2 (mem_pairs.1 hp).1
    · simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact mem_pairs.2 hpx
      · exact mem_pairs.2 hpx.symm
      · exact mem_pairs.2 hpz
  have h4 := card_le_card h3
  rw [card_union_of_disjoint hD, hcard3] at h4
  unfold mu at h2 ⊢
  have := card_le_card h1
  omega
end BrooksTheorem.Aux
