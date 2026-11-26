-- Prove2me | solution 1 for BrooksTheorem.Aux.greedy_reach
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:55.517496+00:00
-- url     : https://prove2.me/submissions/f8104f46-deeb-4aef-a945-a0b7af25b8a2

module
public import Mathlib
public import Definitions.Def_BrooksLib_Greedy
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
public import Theorems.Thm_BrooksTheorem_Aux_greedy_core
attribute [local simp] BrooksTheorem.Aux.mem_nb

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution [DecidableEq V] (H : SimpleGraph V) (k : ℕ) (hdeg : ∀ v, (nb H v).card ≤ k)
    (P : Finset V) (f : V → Fin k)
    (hf : ∀ u ∈ P, ∀ v ∈ P, H.Adj u v → f u ≠ f v) (T : V → Prop)
    (hT : ∀ w ∉ P, T w → (((nb H w).filter (· ∈ P)).image f).card +
       ((nb H w).filter (· ∉ P)).card < k)
    (hreach : ∀ w ∉ P, ∃ n, near H P T n w) :
    ∃ g : V → Fin k, (∀ v ∈ P, g v = f v) ∧ Proper H g := by
  classical
  let r : V → ℕ := fun w => if h : ∃ n, near H P T n w then Nat.find h else 0
  refine greedy_core H k r _ P f rfl hf ?_
  intro w hw
  obtain ⟨n0, hn0⟩ := hreach w hw
  have hex : ∃ n, near H P T n w := ⟨n0, hn0⟩
  have hrw : r w = Nat.find hex := dif_pos hex
  have hspec := Nat.find_spec hex
  have himg := card_image_le (s := (nb H w).filter (· ∈ P)) (f := f)
  have hsplit := card_filter_add_card_filter_not (s := nb H w) (fun u => u ∈ P)
  have hdw := hdeg w
  rcases hm : Nat.find hex with _ | j
  · rw [hm] at hspec
    have := hT w hw hspec
    have hsub : (nb H w).filter (fun u => u ∉ P ∧ r w ≤ r u) ⊆ (nb H w).filter (· ∉ P) := by
      intro u; simp only [mem_filter]; tauto
    have := card_le_card hsub
    omega
  · rw [hm] at hspec
    obtain ⟨u, hwu, huP, hu⟩ := hspec
    have hexu : ∃ n, near H P T n u := ⟨j, hu⟩
    have hru : r u ≤ j := by
      have : r u = Nat.find hexu := dif_pos hexu
      rw [this]; exact Nat.find_min' hexu hu
    have hsub : (nb H w).filter (fun u => u ∉ P ∧ r w ≤ r u) ⊆
        ((nb H w).filter (· ∉ P)).erase u := by
      intro v hv
      simp only [mem_filter, mem_erase] at hv ⊢
      refine ⟨?_, hv.1, hv.2.1⟩
      rintro rfl
      omega
    have hmem : u ∈ (nb H w).filter (· ∉ P) := by simp [hwu, huP]
    have := card_le_card hsub
    rw [card_erase_of_mem hmem] at this
    have hpos := card_pos.mpr ⟨u, hmem⟩
    omega
end BrooksTheorem.Aux
