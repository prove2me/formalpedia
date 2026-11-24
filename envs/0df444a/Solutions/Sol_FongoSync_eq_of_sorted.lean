-- Prove2me | solution 1 for FongoSync.eq_of_sorted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:11.895804+00:00
-- url     : https://prove2.me/submissions/b9f059a2-9567-4169-bff4-475dd02c2631

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_GidSet

set_option autoImplicit false
open FongoSync
namespace FongoSync
theorem _root_.solution {l₁ l₂ : List Gid} (s₁ : l₁.Pairwise (· < ·)) (s₂ : l₂.Pairwise (· < ·))
    (same : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b u => exact absurd ((same b).mpr (.head _)) (by simp)
  | cons a t ih =>
    cases l₂ with
    | nil => exact absurd ((same a).mp (.head _)) (by simp)
    | cons b u =>
      rw [List.pairwise_cons] at s₁ s₂
      have hab : a = b := by
        rcases List.mem_cons.mp ((same a).mp (.head _)) with h | h
        · exact h
        · rcases List.mem_cons.mp ((same b).mpr (.head _)) with h' | h'
          · exact h'.symm
          · exact absurd (Nat.lt_trans (s₂.1 a h) (s₁.1 b h')) (Nat.lt_irrefl b)
      subst hab
      congr 1
      apply ih s₁.2 s₂.2
      intro x
      constructor
      · intro hx
        rcases List.mem_cons.mp ((same x).mp (.tail _ hx)) with h | h
        · subst h; exact absurd (s₁.1 x hx) (Nat.lt_irrefl x)
        · exact h
      · intro hx
        rcases List.mem_cons.mp ((same x).mpr (.tail _ hx)) with h | h
        · subst h; exact absurd (s₂.1 x hx) (Nat.lt_irrefl x)
        · exact h
end FongoSync
