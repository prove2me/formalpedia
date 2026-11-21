-- Prove2me | solution 1 for Champernowne.mem_allWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:37:14.884065+00:00
-- url     : https://prove2.me/submissions/5facb759-b8d9-430d-9eea-d6a6abd62ba5

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_LeanPool_Champernowne_Count

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b k : ℕ} {l : List ℕ} :
    l ∈ allWords b k ↔ l.length = k ∧ ∀ d ∈ l, d < b := by
  induction k generalizing l with
  | zero => cases l <;> simp [allWords]
  | succ k ih =>
    simp only [allWords, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨d, hd, v, hv, rfl⟩
      obtain ⟨hlen, hlt⟩ := ih.mp hv
      refine ⟨by simp [hlen], ?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he'
      · exact hd
      · exact hlt e he'
    · rintro ⟨hlen, hlt⟩
      cases l with
      | nil => simp at hlen
      | cons d v =>
        exact ⟨d, hlt d (List.mem_cons_self ..), v,
          ih.mpr ⟨by simpa using hlen, fun e he => hlt e (List.mem_cons_of_mem d he)⟩,
          rfl⟩
end Champernowne
