-- Prove2me | solution 1 for BrooksTheorem.Aux.greedy_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:28:33.140356+00:00
-- url     : https://prove2.me/submissions/d5180e45-2f77-4923-a0f3-f08ef0810393

module
public import Mathlib
public import Definitions.Def_BrooksLib_Greedy
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
public import Theorems.Thm_BrooksTheorem_Aux_exists_not_mem_of_card_lt
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
theorem _root_.solution [DecidableEq V] (H : SimpleGraph V) (k : ℕ) (r : V → ℕ) :
    ∀ (n : ℕ) (P : Finset V) (f : V → Fin k), Pᶜ.card = n →
    (∀ u ∈ P, ∀ v ∈ P, H.Adj u v → f u ≠ f v) →
    (∀ w ∉ P, (((nb H w).filter (· ∈ P)).image f).card +
       ((nb H w).filter (fun u => u ∉ P ∧ r w ≤ r u)).card < k) →
    ∃ g : V → Fin k, (∀ v ∈ P, g v = f v) ∧ Proper H g := by
  intro n
  induction n with
  | zero =>
    intro P f hn hf _
    have hP : ∀ v, v ∈ P := by
      intro v
      by_contra h
      have : v ∈ Pᶜ := by simpa using h
      rw [Finset.card_eq_zero] at hn
      simp_all
    exact ⟨f, fun _ _ => rfl, fun u v h => hf u (hP u) v (hP v) h⟩
  | succ n ih =>
    intro P f hn hf hc
    have hne : Pᶜ.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨w, hwP, hwmax⟩ := Finset.exists_max_image Pᶜ r hne
    have hwP' : w ∉ P := by simpa using hwP
    have hCk : (((nb H w).filter (· ∈ P)).image f).card < k :=
      lt_of_le_of_lt (Nat.le_add_right _ _) (hc w hwP')
    obtain ⟨col, hcol⟩ := exists_not_mem_of_card_lt _ hCk
    have hcard : (insert w P)ᶜ.card = n := by
      have : (insert w P)ᶜ = Pᶜ.erase w := by ext; simp
      rw [this, card_erase_of_mem hwP]; omega
    have hprop : ∀ u ∈ insert w P, ∀ v ∈ insert w P, H.Adj u v →
        Function.update f w col u ≠ Function.update f w col v := by
      intro u hu v hv huv
      rw [mem_insert] at hu hv
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact absurd huv (H.loopless.irrefl _)
      · have hvw : v ≠ u := fun h => hwP' (h ▸ hv)
        simp only [Function.update_self, Function.update_of_ne hvw]
        intro h
        apply hcol
        rw [h]
        exact mem_image_of_mem f (by simp [hv, huv])
      · have huw : u ≠ v := fun h => hwP' (h ▸ hu)
        simp only [Function.update_self, Function.update_of_ne huw]
        intro h
        apply hcol
        rw [← h]
        exact mem_image_of_mem f (by simp [hu, huv.symm])
      · have huw : u ≠ w := fun h => hwP' (h ▸ hu)
        have hvw : v ≠ w := fun h => hwP' (h ▸ hv)
        simp only [Function.update_of_ne huw, Function.update_of_ne hvw]
        exact hf u hu v hv huv
    have hcond : ∀ w' ∉ insert w P,
        (((nb H w').filter (· ∈ insert w P)).image (Function.update f w col)).card +
          ((nb H w').filter (fun u => u ∉ insert w P ∧ r w' ≤ r u)).card < k := by
      intro w' hw'
      rw [mem_insert, not_or] at hw'
      obtain ⟨hw'w, hw'P⟩ := hw'
      have hrw : r w' ≤ r w := hwmax w' (by simpa using hw'P)
      have hold := hc w' hw'P
      by_cases hadj : H.Adj w' w
      · have h1 : (((nb H w').filter (· ∈ insert w P)).image (Function.update f w col)) ⊆
            insert col (((nb H w').filter (· ∈ P)).image f) := by
          intro c hc'
          simp only [mem_image, mem_filter, mem_nb, mem_insert] at hc'
          obtain ⟨u, ⟨hu1, hu2⟩, rfl⟩ := hc'
          rcases hu2 with rfl | hu2
          · simp
          · have huw : u ≠ w := fun h => hwP' (h ▸ hu2)
            rw [Function.update_of_ne huw]
            exact mem_insert_of_mem (mem_image_of_mem f (by simp [hu1, hu2]))
        have h2 : (nb H w').filter (fun u => u ∉ P ∧ r w' ≤ r u) =
            insert w ((nb H w').filter (fun u => u ∉ insert w P ∧ r w' ≤ r u)) := by
          ext u
          simp only [mem_filter, mem_nb, mem_insert, not_or]
          constructor
          · rintro ⟨hu1, hu2, hu3⟩
            by_cases huw : u = w
            · left; exact huw
            · right; exact ⟨hu1, ⟨huw, hu2⟩, hu3⟩
          · rintro (rfl | ⟨hu1, ⟨_, hu2⟩, hu3⟩)
            · exact ⟨hadj, hwP', hrw⟩
            · exact ⟨hu1, hu2, hu3⟩
        have h3 : w ∉ (nb H w').filter (fun u => u ∉ insert w P ∧ r w' ≤ r u) := by
          simp
        rw [h2, card_insert_of_notMem h3] at hold
        have := (card_le_card h1).trans (card_insert_le _ _)
        omega
      · have h1 : (nb H w').filter (· ∈ insert w P) = (nb H w').filter (· ∈ P) := by
          ext u
          simp only [mem_filter, mem_nb, mem_insert]
          constructor
          · rintro ⟨hu1, rfl | hu2⟩
            · exact absurd hu1 hadj
            · exact ⟨hu1, hu2⟩
          · rintro ⟨hu1, hu2⟩; exact ⟨hu1, Or.inr hu2⟩
        have h1' : ((nb H w').filter (· ∈ P)).image (Function.update f w col) =
            ((nb H w').filter (· ∈ P)).image f := by
          apply image_congr
          intro u hu
          simp only [coe_filter, mem_nb, Set.mem_ofPred_eq] at hu
          have huw : u ≠ w := fun h => hwP' (h ▸ hu.2)
          simp [Function.update_of_ne huw]
        have h2 : (nb H w').filter (fun u => u ∉ insert w P ∧ r w' ≤ r u) =
            (nb H w').filter (fun u => u ∉ P ∧ r w' ≤ r u) := by
          ext u
          simp only [mem_filter, mem_nb, mem_insert, not_or]
          constructor
          · rintro ⟨hu1, ⟨_, hu2⟩, hu3⟩; exact ⟨hu1, hu2, hu3⟩
          · rintro ⟨hu1, hu2, hu3⟩
            exact ⟨hu1, ⟨fun h => hadj (h ▸ hu1), hu2⟩, hu3⟩
        rw [h1, h1', h2]
        exact hold
    obtain ⟨g, hg1, hg2⟩ := ih (insert w P) (Function.update f w col) hcard hprop hcond
    refine ⟨g, fun v hv => ?_, hg2⟩
    rw [hg1 v (mem_insert_of_mem hv)]
    simp [Function.update, show v ≠ w from fun h => hwP' (h ▸ hv)]
end BrooksTheorem.Aux
