-- Prove2me | solution 1 for FongoSync.mem_insertGid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:59:55.002879+00:00
-- url     : https://prove2.me/submissions/7d859109-8147-4f51-b853-c6ce90a6856b

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_GidSet

set_option autoImplicit false
open FongoSync
namespace FongoSync
theorem _root_.solution {g x : Gid} {l : List Gid} : x ∈ insertGid g l ↔ x = g ∨ x ∈ l := by
  induction l with
  | nil => simp [insertGid]
  | cons h t ih =>
    unfold insertGid
    by_cases h₁ : g < h
    · simp [h₁]
    · by_cases h₂ : g = h
      · subst h₂; simp [h₁]
      · simp only [h₁, h₂, ↓reduceIte, List.mem_cons, ih]
        constructor
        · rintro (h | h | h) <;> simp_all
        · rintro (h | h | h) <;> simp_all
end FongoSync
