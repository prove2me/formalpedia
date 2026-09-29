-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_domain_context
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T09:43:44.963978+00:00
-- url     : https://prove2.me/submissions/4490f531-9e84-4fbb-91a4-7aebe79be30f

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

namespace M7EarlyCtx

/-- two singleton suffixes of the same word agree -/
lemma last_unique {α : Type*} {w : List α} {a b : α} (ha : [a] <:+ w) (hb : [b] <:+ w) :
    a = b := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  have h : s ++ [a] = t ++ [b] := by rw [hs, ht]
  have h2 := (List.append_inj' h rfl).2
  simpa using h2

lemma normalize_cases (p : LowerPair) :
    lowerNormalize p = p ∨ lowerNormalize p = (p.2, p.1) := by
  unfold lowerNormalize
  split_ifs <;> simp

/-- the context fit for a one-letter left context and a right side ending in `3,1`. -/
lemma key (q : LowerPair) (c : ℕ+)
    (he : ([c] : List ℕ+) <:+ q.1)
    (hL : ¬ (([3,1] : List ℕ+) <:+ q.1))
    (hR : ([3,1] : List ℕ+) <:+ q.2)
    (hpar : q.1.length % 2 = q.2.length % 2) :
    lowerHistoryContextFits q ⟨([c],[3,1]),(false,false)⟩ := by
  have h1suf : ([1] : List ℕ+) <:+ q.2 :=
    List.IsSuffix.trans (⟨[3], rfl⟩ : ([1] : List ℕ+) <:+ [3,1]) hR
  refine ⟨⟨he, ?_, ?_⟩, ⟨hR, ?_, ?_⟩, ?_⟩
  · constructor
    · intro hx
      have h3c : (3 : ℕ+) = c := last_unique hx he
      show ([3] : List ℕ+) <:+ [c]
      rw [← h3c]
    · intro hx
      have : ([3] : List ℕ+) = [c] := List.IsSuffix.eq_of_length hx (by simp)
      rw [this]
      exact he
  · refine iff_of_false hL (fun hx => ?_)
    have := List.IsSuffix.length_le hx
    simp at this
  · refine iff_of_false (fun hx => ?_) (fun hx => ?_)
    · exact absurd (last_unique hx h1suf) (by decide)
    · exact absurd (last_unique hx (⟨[3], rfl⟩ : ([1] : List ℕ+) <:+ [3,1])) (by decide)
  · exact iff_of_true hR (List.suffix_refl _)
  · show (decide (q.1.length % 2 = 1)).xor false = (decide (q.2.length % 2 = 1)).xor false
    rw [hpar]

end M7EarlyCtx

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (C : LowerEarlyTerminalCatalog)
    (hc : C ∈ [lowerEarlyTerminalEarly3,lowerEarlyTerminalState1,lowerEarlyTerminalState2,lowerEarlyTerminalTerminal3])
    (he : lowerEnds (lowerNormalize p).1 C.leftContext) : lowerEarlyTerminalMatches p C := by
  obtain ⟨hmix, -, -, hL, hR, -, -⟩ := hd
  unfold lowerMixed at hmix
  unfold lowerL at hL
  unfold lowerR at hR
  unfold lowerEnds at he hL hR
  have hpar : (lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2 := by
    have hp : p.1.length % 2 = p.2.length % 2 := by omega
    rcases M7EarlyCtx.normalize_cases p with h | h <;> rw [h]
    · exact hp
    · exact hp.symm
  have hctx : C.leftContext = ([3] : List ℕ+) ∨ C.leftContext = ([1] : List ℕ+) ∨
      C.leftContext = ([2] : List ℕ+) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr (Or.inl (by rw [h]; rfl))
    · exact Or.inr (Or.inr (by rw [h]; rfl))
    · exact Or.inl (by rw [h]; rfl)
  show lowerHistoryContextFits (lowerNormalize p) ⟨(C.leftContext,[3,1]),(false,false)⟩
  rcases hctx with h | h | h <;> rw [h] <;> rw [h] at he <;>
    exact M7EarlyCtx.key _ _ he hL hR hpar
