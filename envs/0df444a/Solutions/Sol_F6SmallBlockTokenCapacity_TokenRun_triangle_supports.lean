-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.triangle_supports
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:31:05.301532+00:00
-- url     : https://prove2.me/submissions/2c6f52ae-8230-481b-8dd9-8bc91679b77e

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_mem_participationSteps
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_pair_of_card_two_mem
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_three_membership_sum
attribute [local simp] F6SmallBlockTokenCapacity.TokenRun.mem_participationSteps

set_option autoImplicit true
open scoped BigOperators
open Classical
noncomputable section
open F6SmallBlockTokenCapacity
variable {B W : Type*} [Fintype B] [Fintype W] {q : ℕ}
open F6SmallBlockTokenCapacity.TokenRun
variable (R : TokenRun B W q)
namespace F6SmallBlockTokenCapacity.TokenRun
theorem _root_.solution (S : Fin 3 → Finset B) (hB : Fintype.card B = 3)
    (hs : ∀ i, (S i).card = 2)
    (hc : ∀ b : B,
      ((Finset.univ : Finset (Fin 3)).filter (fun i => b ∈ S i)).card = 2) :
    ∃ x a b : B, x ≠ a ∧ x ≠ b ∧ a ≠ b ∧
      S 0 = {x, a} ∧ S 1 = {a, b} ∧ S 2 = {x, b} := by
  classical
  have hsum (b : B) :
      (if b ∈ S 0 then 1 else 0) + (if b ∈ S 1 then 1 else 0) +
        (if b ∈ S 2 then 1 else 0) = 2 := by
    rw [← three_membership_sum]
    exact hc b
  have hinter : 0 < (S 0 ∩ S 2).card := by
    have hu := (S 0 ∪ S 2).card_le_univ
    have hi := Finset.card_union_add_card_inter (S 0) (S 2)
    rw [hs 0, hs 2] at hi
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hinter
  obtain ⟨hx0, hx2⟩ := Finset.mem_inter.mp hx
  have hx1 : x ∉ S 1 := by
    intro h
    have hh := hsum x
    simp [hx0, h, hx2] at hh
  obtain ⟨a, hxa, h0⟩ := pair_of_card_two_mem (S 0) (hs 0) x hx0
  obtain ⟨b, hxb, h2⟩ := pair_of_card_two_mem (S 2) (hs 2) x hx2
  have h1compl : S 1 = Finset.univ.erase x := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro hcx
      exact hx1 (hcx ▸ hc)
    · simp [hB, hs 1]
  have ha1 : a ∈ S 1 := by simp [h1compl, hxa.symm]
  have hb1 : b ∈ S 1 := by simp [h1compl, hxb.symm]
  have hab : a ≠ b := by
    intro heq
    have ha0 : a ∈ S 0 := by simp [h0]
    have ha2 : a ∈ S 2 := by simp [h2, heq]
    have hh := hsum a
    simp [ha0, ha1, ha2] at hh
  have h1 : S 1 = {a, b} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact ha1
      · exact hb1
    · simp [hs 1, hab]
  exact ⟨x, a, b, hxa, hxb, hab, h0, h1, h2⟩
end F6SmallBlockTokenCapacity.TokenRun
