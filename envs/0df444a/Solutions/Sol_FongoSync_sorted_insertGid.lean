-- Prove2me | solution 1 for FongoSync.sorted_insertGid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:07.20735+00:00
-- url     : https://prove2.me/submissions/b43237ba-9d12-4472-a0c1-86591779c29d

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_GidSet
import Theorems.Thm_FongoSync_mem_insertGid

set_option autoImplicit false
open FongoSync
namespace FongoSync
theorem _root_.solution {g : Gid} {l : List Gid} (s : l.Pairwise (· < ·)) :
    (insertGid g l).Pairwise (· < ·) := by
  induction l with
  | nil => simp [insertGid]
  | cons h t ih =>
    rw [List.pairwise_cons] at s
    unfold insertGid
    by_cases h₁ : g < h
    · simp only [h₁, ↓reduceIte, List.pairwise_cons, List.mem_cons]
      refine ⟨?_, s.1, s.2⟩
      rintro x (rfl | hx)
      · exact h₁
      · exact Nat.lt_trans h₁ (s.1 x hx)
    · by_cases h₂ : g = h
      · subst h₂; simp only [Nat.lt_irrefl, ↓reduceIte, List.pairwise_cons]; exact s
      · simp only [h₁, h₂, ↓reduceIte, List.pairwise_cons]
        refine ⟨fun x hx => ?_, ih s.2⟩
        rcases mem_insertGid.mp hx with rfl | hx
        · exact Nat.lt_of_le_of_ne (Nat.not_lt.mp h₁) (Ne.symm h₂)
        · exact s.1 x hx
end FongoSync
