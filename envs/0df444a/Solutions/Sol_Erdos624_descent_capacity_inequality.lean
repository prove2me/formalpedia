-- Prove2me | solution 1 for Erdos624.descent_capacity_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:36:54.215761+00:00
-- url     : https://prove2.me/submissions/1d9c175a-2e3a-48d6-ac90-e0f1e9bc37d2

import Mathlib
open Finset

namespace E624R14D
open Finset

theorem descent {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (b a : ℕ) (hb : ∀ A, #(L A) ≤ b) (S : Finset C)
    (V : C → Finset U)
    (hcov : ∀ u ∈ S, ∀ Y ⊆ V u, #Y = a → ∃ A ⊆ Y, A.Nonempty ∧ u ∈ L A) :
    ∑ u ∈ S, (#(V u)).choose a ≤ b * (2 ^ a - 1) * (Fintype.card U).choose a := by
  classical
  set 𝒴 := (univ : Finset U).powersetCard a with h𝒴
  have h1 : ∀ u ∈ S, (#(V u)).choose a ≤
      #(𝒴.filter (fun Y => ∃ A ⊆ Y, A.Nonempty ∧ u ∈ L A)) := by
    intro u hu
    rw [← card_powersetCard]
    apply card_le_card
    intro Y hY
    rw [mem_powersetCard] at hY
    rw [mem_filter, h𝒴, mem_powersetCard]
    exact ⟨⟨subset_univ _, hY.2⟩, hcov u hu Y hY.1 hY.2⟩
  have h2 : ∑ u ∈ S, #(𝒴.filter (fun Y => ∃ A ⊆ Y, A.Nonempty ∧ u ∈ L A)) =
      ∑ Y ∈ 𝒴, #(S.filter (fun u => ∃ A ⊆ Y, A.Nonempty ∧ u ∈ L A)) := by
    simp only [card_filter]; exact sum_comm
  have h3 : ∀ Y ∈ 𝒴, #(S.filter (fun u => ∃ A ⊆ Y, A.Nonempty ∧ u ∈ L A)) ≤ b * (2 ^ a - 1) := by
    intro Y hY
    rw [h𝒴, mem_powersetCard] at hY
    calc #(S.filter (fun u => ∃ A ⊆ Y, A.Nonempty ∧ u ∈ L A))
        ≤ #((Y.powerset.erase ∅).biUnion L) := by
          apply card_le_card
          intro u hu
          obtain ⟨A, hAY, hne, huA⟩ := (mem_filter.1 hu).2
          exact mem_biUnion.2 ⟨A, mem_erase.2 ⟨hne.ne_empty, mem_powerset.2 hAY⟩, huA⟩
      _ ≤ ∑ A ∈ Y.powerset.erase ∅, #(L A) := card_biUnion_le
      _ ≤ ∑ _A ∈ Y.powerset.erase ∅, b := sum_le_sum fun A _ => hb A
      _ = b * (2 ^ a - 1) := by
          rw [sum_const, smul_eq_mul, card_erase_of_mem (empty_mem_powerset _), card_powerset,
            hY.2, mul_comm]
  calc ∑ u ∈ S, (#(V u)).choose a
      ≤ ∑ u ∈ S, #(𝒴.filter (fun Y => ∃ A ⊆ Y, A.Nonempty ∧ u ∈ L A)) := sum_le_sum h1
    _ = _ := h2
    _ ≤ ∑ _Y ∈ 𝒴, b * (2 ^ a - 1) := sum_le_sum h3
    _ = b * (2 ^ a - 1) * (Fintype.card U).choose a := by
        rw [sum_const, smul_eq_mul, h𝒴, card_powersetCard, card_univ, mul_comm]
end E624R14D

namespace Erdos624

theorem descent_capacity_inequality {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (b a : ℕ) (hb : ∀ A, #(L A) ≤ b) (S : Finset C)
    (V : C → Finset U)
    (hcov : ∀ u ∈ S, ∀ Y ⊆ V u, #Y = a → ∃ A ⊆ Y, A.Nonempty ∧ u ∈ L A) :
    ∑ u ∈ S, (#(V u)).choose a ≤ b * (2 ^ a - 1) * (Fintype.card U).choose a := by
  exact E624R14D.descent L b a hb S V hcov

end Erdos624

open Finset

theorem solution {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (b a : ℕ) (hb : ∀ A, #(L A) ≤ b) (S : Finset C)
    (V : C → Finset U)
    (hcov : ∀ u ∈ S, ∀ Y ⊆ V u, #Y = a → ∃ A ⊆ Y, A.Nonempty ∧ u ∈ L A) :
    ∑ u ∈ S, (#(V u)).choose a ≤ b * (2 ^ a - 1) * (Fintype.card U).choose a :=
  Erdos624.descent_capacity_inequality L b a hb S V hcov
