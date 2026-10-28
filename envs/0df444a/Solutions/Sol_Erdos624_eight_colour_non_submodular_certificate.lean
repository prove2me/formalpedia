-- Prove2me | solution 1 for Erdos624.eight_colour_non_submodular_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:36:51.418014+00:00
-- url     : https://prove2.me/submissions/4cfa1c16-fdf0-4602-b8f1-73b94cae156d

import Mathlib
open Finset

namespace E624R14E
open Finset

def tbl : List ℕ := [1, 2, 4, 64, 8, 36, 80, 128, 16, 32, 130, 8, 132, 64, 96, 0, 16, 192, 8, 32, 32, 24, 130, 0, 66, 12, 32, 0, 2, 0, 0, 0, 96, 136, 10, 16, 4, 16, 128, 0, 136, 4, 1, 0, 18, 0, 0, 0, 2, 4, 160, 0, 136, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 160, 12, 18, 32, 66, 17, 32, 0, 1, 64, 72, 0, 4, 0, 0, 0, 72, 32, 32, 0, 4, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 20, 64, 1, 0, 8, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 16, 160, 8, 18, 136, 2, 0, 12, 192, 2, 0, 34, 0, 0, 0, 132, 40, 2, 0, 136, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 2, 4, 16, 0, 136, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 1, 64, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def LL (A : Finset (Fin 8)) : Finset (Fin 8) :=
  univ.filter (fun c : Fin 8 => Nat.testBit (tbl.getD (∑ i ∈ A, 2 ^ (i : ℕ)) 0) c)

def chi (A : Finset (Fin 8)) : Fin 8 → ZMod 2 := fun i => if i ∈ A then 1 else 0

lemma forced (Z : Submodule (ZMod 2) (Fin 8 → ZMod 2)) (Y A0 : Finset (Fin 8))
    (huniq : ∀ A ⊆ Y, A.Nonempty → 2 ∈ LL A → A = A0)
    (h : ∃ A ⊆ Y, A.Nonempty ∧ 2 ∈ LL A ∧ (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) :
    chi A0 ∈ Z := by
  obtain ⟨A, hAY, hne, hu, hZ⟩ := h
  rw [← huniq A hAY hne hu]; exact hZ

set_option maxRecDepth 100000

lemma u034 : ∀ A ⊆ ({0, 3, 4} : Finset (Fin 8)), A.Nonempty → 2 ∈ LL A → A = {0, 3, 4} := by
  decide
lemma u037 : ∀ A ⊆ ({0, 3, 7} : Finset (Fin 8)), A.Nonempty → 2 ∈ LL A → A = {3, 7} := by
  decide
lemma u045 : ∀ A ⊆ ({0, 4, 5} : Finset (Fin 8)), A.Nonempty → 2 ∈ LL A → A = {0, 4, 5} := by
  decide
lemma u356 : ∀ A ⊆ ({3, 5, 6} : Finset (Fin 8)), A.Nonempty → 2 ∈ LL A → A = {5, 6} := by
  decide
lemma m06 : 2 ∈ LL {0, 6} := by decide
lemma m47 : 2 ∈ LL {4, 7} := by decide
lemma e0 : (Pi.single 0 1 : Fin 8 → ZMod 2) = chi {0, 3, 4} + chi {3, 7} + chi {4, 7} := by decide
lemma e6 : (Pi.single 6 1 : Fin 8 → ZMod 2) =
    chi {0, 6} + chi {0, 3, 4} + chi {3, 7} + chi {4, 7} := by decide
lemma e4 : (Pi.single 4 1 : Fin 8 → ZMod 2) = chi {0, 4, 5} + chi {5, 6} + chi {0, 6} := by decide
lemma e7 : (Pi.single 7 1 : Fin 8 → ZMod 2) =
    chi {0, 4, 5} + chi {5, 6} + chi {0, 6} + chi {4, 7} := by decide

lemma anch (Z : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (h : ∀ A ⊆ ({0, 4, 6, 7} : Finset (Fin 8)), A.Nonempty → 2 ∈ LL A →
      (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) :
    chi {0, 6} ∈ Z ∧ chi {4, 7} ∈ Z :=
  ⟨h {0, 6} (by decide) (by decide) m06, h {4, 7} (by decide) (by decide) m47⟩

theorem eight :
    ∃ L : Finset (Fin 8) → Finset (Fin 8),
      (∀ A, #(L A) ≤ 2) ∧ (∀ A, 3 < #A → L A = ∅) ∧ L ∅ = {0} ∧
      (∀ Y : Finset (Fin 8), #Y = 3 → ∀ c : Fin 8, ∃ A ⊆ Y, c ∈ L A) ∧
      (∀ A ⊆ ({0, 4, 6, 7} : Finset (Fin 8)), A.Nonempty → 2 ∈ L A →
        A = {0, 6} ∨ A = {4, 7}) ∧
      (∀ Y ⊆ ({0, 4, 5, 6, 7} : Finset (Fin 8)), #Y = 3 →
        ∃ A ⊆ Y, A.Nonempty ∧ 2 ∈ L A ∧ A ≠ {5, 6} ∧
          Even #(A ∩ {0, 5, 6}) ∧ Even #(A ∩ {4, 5, 7})) ∧
      (∀ Y ⊆ ({0, 3, 4, 6, 7} : Finset (Fin 8)), #Y = 3 →
        ∃ A ⊆ Y, A.Nonempty ∧ 2 ∈ L A ∧ Even #(A ∩ {3, 4, 7})) ∧
      (∀ Z : Submodule (ZMod 2) (Fin 8 → ZMod 2),
        (∀ A ⊆ ({0, 4, 6, 7} : Finset (Fin 8)), A.Nonempty → 2 ∈ L A →
          (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) →
        (∀ Y ⊆ ({0, 3, 4, 6, 7} : Finset (Fin 8)), #Y = 3 →
          ∃ A ⊆ Y, A.Nonempty ∧ 2 ∈ L A ∧ (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) →
        (Pi.single 0 1 : Fin 8 → ZMod 2) ∈ Z) ∧
      (∀ Z : Submodule (ZMod 2) (Fin 8 → ZMod 2),
        (∀ A ⊆ ({0, 4, 6, 7} : Finset (Fin 8)), A.Nonempty → 2 ∈ L A →
          (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) →
        (∀ Y ⊆ ({0, 3, 4, 5, 6, 7} : Finset (Fin 8)), #Y = 3 →
          ∃ A ⊆ Y, A.Nonempty ∧ 2 ∈ L A ∧ (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) →
        ∀ t ∈ ({0, 4, 6, 7} : Finset (Fin 8)), (Pi.single t 1 : Fin 8 → ZMod 2) ∈ Z) := by
  refine ⟨LL, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    ?_, ?_⟩
  · intro Z ha hc
    obtain ⟨_, h47⟩ := anch Z ha
    have h1 := forced Z _ _ u034 (hc {0, 3, 4} (by decide) (by decide))
    have h2 := forced Z _ _ u037 (hc {0, 3, 7} (by decide) (by decide))
    rw [e0]; exact Z.add_mem (Z.add_mem h1 h2) h47
  · intro Z ha hc
    obtain ⟨h06, h47⟩ := anch Z ha
    have h1 := forced Z _ _ u034 (hc {0, 3, 4} (by decide) (by decide))
    have h2 := forced Z _ _ u037 (hc {0, 3, 7} (by decide) (by decide))
    have h3 := forced Z _ _ u045 (hc {0, 4, 5} (by decide) (by decide))
    have h4 := forced Z _ _ u356 (hc {3, 5, 6} (by decide) (by decide))
    intro t ht
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · rw [e0]; exact Z.add_mem (Z.add_mem h1 h2) h47
    · rw [e4]; exact Z.add_mem (Z.add_mem h3 h4) h06
    · rw [e6]; exact Z.add_mem (Z.add_mem (Z.add_mem h06 h1) h2) h47
    · rw [e7]; exact Z.add_mem (Z.add_mem (Z.add_mem h3 h4) h06) h47
end E624R14E

namespace Erdos624

theorem eight_colour_non_submodular_certificate :
    ∃ L : Finset (Fin 8) → Finset (Fin 8),
      (∀ A, #(L A) ≤ 2) ∧ (∀ A, 3 < #A → L A = ∅) ∧ L ∅ = {0} ∧
      (∀ Y : Finset (Fin 8), #Y = 3 → ∀ c : Fin 8, ∃ A ⊆ Y, c ∈ L A) ∧
      (∀ A ⊆ ({0, 4, 6, 7} : Finset (Fin 8)), A.Nonempty → 2 ∈ L A →
        A = {0, 6} ∨ A = {4, 7}) ∧
      (∀ Y ⊆ ({0, 4, 5, 6, 7} : Finset (Fin 8)), #Y = 3 →
        ∃ A ⊆ Y, A.Nonempty ∧ 2 ∈ L A ∧ A ≠ {5, 6} ∧
          Even #(A ∩ {0, 5, 6}) ∧ Even #(A ∩ {4, 5, 7})) ∧
      (∀ Y ⊆ ({0, 3, 4, 6, 7} : Finset (Fin 8)), #Y = 3 →
        ∃ A ⊆ Y, A.Nonempty ∧ 2 ∈ L A ∧ Even #(A ∩ {3, 4, 7})) ∧
      (∀ Z : Submodule (ZMod 2) (Fin 8 → ZMod 2),
        (∀ A ⊆ ({0, 4, 6, 7} : Finset (Fin 8)), A.Nonempty → 2 ∈ L A →
          (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) →
        (∀ Y ⊆ ({0, 3, 4, 6, 7} : Finset (Fin 8)), #Y = 3 →
          ∃ A ⊆ Y, A.Nonempty ∧ 2 ∈ L A ∧ (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) →
        (Pi.single 0 1 : Fin 8 → ZMod 2) ∈ Z) ∧
      (∀ Z : Submodule (ZMod 2) (Fin 8 → ZMod 2),
        (∀ A ⊆ ({0, 4, 6, 7} : Finset (Fin 8)), A.Nonempty → 2 ∈ L A →
          (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) →
        (∀ Y ⊆ ({0, 3, 4, 5, 6, 7} : Finset (Fin 8)), #Y = 3 →
          ∃ A ⊆ Y, A.Nonempty ∧ 2 ∈ L A ∧ (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) →
        ∀ t ∈ ({0, 4, 6, 7} : Finset (Fin 8)), (Pi.single t 1 : Fin 8 → ZMod 2) ∈ Z) := by
  exact E624R14E.eight

end Erdos624

open Finset

theorem solution :
    ∃ L : Finset (Fin 8) → Finset (Fin 8),
      (∀ A, #(L A) ≤ 2) ∧ (∀ A, 3 < #A → L A = ∅) ∧ L ∅ = {0} ∧
      (∀ Y : Finset (Fin 8), #Y = 3 → ∀ c : Fin 8, ∃ A ⊆ Y, c ∈ L A) ∧
      (∀ A ⊆ ({0, 4, 6, 7} : Finset (Fin 8)), A.Nonempty → 2 ∈ L A →
        A = {0, 6} ∨ A = {4, 7}) ∧
      (∀ Y ⊆ ({0, 4, 5, 6, 7} : Finset (Fin 8)), #Y = 3 →
        ∃ A ⊆ Y, A.Nonempty ∧ 2 ∈ L A ∧ A ≠ {5, 6} ∧
          Even #(A ∩ {0, 5, 6}) ∧ Even #(A ∩ {4, 5, 7})) ∧
      (∀ Y ⊆ ({0, 3, 4, 6, 7} : Finset (Fin 8)), #Y = 3 →
        ∃ A ⊆ Y, A.Nonempty ∧ 2 ∈ L A ∧ Even #(A ∩ {3, 4, 7})) ∧
      (∀ Z : Submodule (ZMod 2) (Fin 8 → ZMod 2),
        (∀ A ⊆ ({0, 4, 6, 7} : Finset (Fin 8)), A.Nonempty → 2 ∈ L A →
          (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) →
        (∀ Y ⊆ ({0, 3, 4, 6, 7} : Finset (Fin 8)), #Y = 3 →
          ∃ A ⊆ Y, A.Nonempty ∧ 2 ∈ L A ∧ (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) →
        (Pi.single 0 1 : Fin 8 → ZMod 2) ∈ Z) ∧
      (∀ Z : Submodule (ZMod 2) (Fin 8 → ZMod 2),
        (∀ A ⊆ ({0, 4, 6, 7} : Finset (Fin 8)), A.Nonempty → 2 ∈ L A →
          (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) →
        (∀ Y ⊆ ({0, 3, 4, 5, 6, 7} : Finset (Fin 8)), #Y = 3 →
          ∃ A ⊆ Y, A.Nonempty ∧ 2 ∈ L A ∧ (fun i => if i ∈ A then (1 : ZMod 2) else 0) ∈ Z) →
        ∀ t ∈ ({0, 4, 6, 7} : Finset (Fin 8)), (Pi.single t 1 : Fin 8 → ZMod 2) ∈ Z) :=
  Erdos624.eight_colour_non_submodular_certificate 
