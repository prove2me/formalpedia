-- Prove2me | solution 1 for FongoSync.isCanonical_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:37.684318+00:00
-- url     : https://prove2.me/submissions/4f1f63c5-2e63-4af7-a814-dc7c4c277ee1

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
import Theorems.Thm_FongoSync_Connected_mono
import Theorems.Thm_FongoSync_label_eq_of_connected
import Theorems.Thm_FongoSync_connected_of_label_eq
import Theorems.Thm_FongoSync_label_le

set_option autoImplicit false
open FongoSync
variable {P : List Edge} {L : Gid → Gid} (inv : ∀ g, IsCanonical P g (L g))
include inv
namespace FongoSync
theorem _root_.solution (e : Edge) (g : Gid) :
    IsCanonical (P ++ [e]) g (union L e g) := by
  have sub : ∀ x ∈ P, x ∈ P ++ [e] := fun x hx => List.mem_append_left _ hx
  have new : Connected (P ++ [e]) e.1 e.2 := .edge (by simp)
  -- the labels after the union are constant on the new groups
  have same : ∀ {x y}, Connected (P ++ [e]) x y → union L e x = union L e y := by
    intro x y c
    induction c with
    | refl => rfl
    | edge he =>
      rcases List.mem_append.mp he with he | he
      · simp only [union, label_eq_of_connected inv (.edge he)]
      · simp only [List.mem_singleton] at he
        subst he
        simp [union]
    | symm _ ih => exact ih.symm
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  -- and never above the gid
  have below : ∀ x, union L e x ≤ x := by
    intro x
    dsimp only [union]
    split
    · rename_i hx
      have := label_le inv x
      rcases hx with hx | hx
      · exact Nat.le_trans (Nat.min_le_left _ _) (hx ▸ this)
      · exact Nat.le_trans (Nat.min_le_right _ _) (hx ▸ this)
    · exact label_le inv x
  refine ⟨?_, fun h c => (same c) ▸ below h⟩
  -- the new label is in the group
  dsimp only [union]
  by_cases ha : L g = L e.1
  · have g1 : Connected (P ++ [e]) g e.1 := (connected_of_label_eq inv ha).mono sub
    simp only [ha, true_or, ↓reduceIte]
    rcases Nat.le_total (L e.1) (L e.2) with le | le
    · rw [Nat.min_eq_left le]; exact ha ▸ ((inv g).1.mono sub)
    · rw [Nat.min_eq_right le]; exact .trans g1 (.trans new ((inv e.2).1.mono sub))
  · by_cases hb : L g = L e.2
    · have g2 : Connected (P ++ [e]) g e.2 := (connected_of_label_eq inv hb).mono sub
      simp only [hb, or_true, ↓reduceIte]
      rcases Nat.le_total (L e.1) (L e.2) with le | le
      · rw [Nat.min_eq_left le]; exact .trans g2 (.trans (.symm new) ((inv e.1).1.mono sub))
      · rw [Nat.min_eq_right le]; exact hb ▸ ((inv g).1.mono sub)
    · simp only [ha, hb, or_self, ↓reduceIte]
      exact (inv g).1.mono sub
end FongoSync
