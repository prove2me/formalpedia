-- Prove2me | solution 1 for Freiman.lowerHistory_structural_generation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-11T02:25:06.308302+00:00
-- url     : https://prove2.me/submissions/b742aa72-4dc1-4d5b-bcb0-21ee298bc74c

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

set_option autoImplicit false

private theorem au_walk_terminal (cat : LowerHistoryCatalog) (ctx : List ℕ+)
    (entry : LowerLabel) (wide : Bool) (s : LowerHistoryState)
    (steps : List (LowerLabel × Bool)) (fuel : ℕ)
    (ht : lowerHistoryTerminal cat s = true) :
    (cat,ctx,entry,wide,steps) ∈ lowerHistoryWalkKeys cat ctx entry wide s steps fuel := by
  cases fuel with
  | zero =>
    change _ ∈ if lowerHistoryTerminal cat s then [(cat,ctx,entry,wide,steps)] else []
    simp only [ht, Bool.true_eq, if_true, List.mem_singleton]
  | succ fuel =>
    change _ ∈ (if lowerHistoryTerminal cat s then [(cat,ctx,entry,wide,steps)] else []) ++ _
    apply List.mem_append.mpr
    apply Or.inl
    simp only [ht, Bool.true_eq, if_true, List.mem_singleton]

private theorem au_walk_complete (cat : LowerHistoryCatalog) (ctx : List ℕ+)
    (entry : LowerLabel) (wide : Bool) (s : LowerHistoryState)
    (done suffix : List (LowerLabel × Bool)) (fuel : ℕ)
    (hlen : suffix.length ≤ fuel) (hlegal : lowerHistoryLegalSteps s suffix)
    (ht : lowerHistoryTerminal cat
      (suffix.foldl (fun q step => lowerHistoryAdvance q step.1 step.2) s) = true) :
    (cat,ctx,entry,wide,done ++ suffix) ∈
      lowerHistoryWalkKeys cat ctx entry wide s done fuel := by
  induction suffix generalizing s done fuel with
  | nil =>
    simpa only [List.append_nil] using
      au_walk_terminal cat ctx entry wide s done fuel ht
  | cons step tail ih =>
    rcases step with ⟨l, reflect⟩
    cases fuel with
    | zero =>
      simp only [List.length_cons] at hlen
      omega
    | succ fuel =>
      have hstep : lowerHistoryStepLegal s l reflect ∧
          lowerHistoryLegalSteps (lowerHistoryAdvance s l reflect) tail := hlegal
      have htail : tail.length ≤ fuel := by
        simpa only [List.length_cons, Nat.succ_le_succ_iff] using hlen
      have ht' : lowerHistoryTerminal cat
          (tail.foldl (fun q step => lowerHistoryAdvance q step.1 step.2)
            (lowerHistoryAdvance s l reflect)) = true := ht
      have hrec := ih (s := lowerHistoryAdvance s l reflect)
        (done := done ++ [(l,reflect)]) (fuel := fuel) htail hstep.2 ht'
      change _ ∈ (if lowerHistoryTerminal cat s then [(cat,ctx,entry,wide,done)] else []) ++ _
      apply List.mem_append.mpr
      apply Or.inr
      apply List.mem_flatMap.mpr
      refine ⟨l, hstep.1.1, ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨reflect, ?_, ?_⟩
      · cases reflect <;> simp only [List.mem_cons, List.not_mem_nil, or_false,
          Bool.false_eq_true, Bool.true_eq_false, or_true, true_or]
      · rw [if_pos hstep.1]
        simpa only [List.append_assoc, List.singleton_append] using hrec

private theorem au_structural_terminal (p : LowerHistoryPath) (hp : lowerHistoryStructural p) :
    lowerHistoryTerminal p.catalog (lowerHistoryFinalState p) = true := by
  have hmarked : (lowerHistoryFinalState p).markedDone = true := hp.2.2.2.1.1
  have hparity : (lowerHistoryFinalState p).context.parity = p.finalParity :=
    hp.2.2.2.1.2.2.1
  have hwide : (lowerHistoryFinalState p).wider = p.finalWider := hp.2.2.2.1.2.2.2
  have hrow := hp.2.2.2.2
  cases hc : p.catalog <;>
    simp only [hc, reduceCtorEq, if_true, if_false, false_and, true_and,
      false_or, or_false] at hrow <;>
    simp only [lowerHistoryTerminal, hc, hmarked, hparity, hwide, Bool.true_and]
  all_goals
    simp only [hrow.2.1, hrow.2.2, decide_true, Bool.true_and, Bool.not_false]

theorem solution (p : LowerHistoryPath) (hp : lowerHistoryStructural p) :
    lowerHistoryPathKey p ∈ lowerHistoryGeneratedKeys p.catalog := by
  have hchoices :
      p.context ∈ (if p.catalog = .initial then [[2],[3]] else lowerHistoryContextWords) ∧
      p.entry ∈ (if p.catalog = .initial then
        [([1],[]),([2],[1]),([3],[1])] else [([2],[3])]) := by
    have hc := hp.2.1
    by_cases hi : p.catalog = .initial
    · simpa only [if_pos hi] using hc
    · simp only [if_neg hi] at hc ⊢
      exact ⟨hc.1, List.mem_singleton.mpr hc.2⟩
  unfold lowerHistoryGeneratedKeys
  apply List.mem_flatMap.mpr
  refine ⟨p.context, hchoices.1, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨p.entry, hchoices.2, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨p.initialWider, ?_, ?_⟩
  · cases p.initialWider <;> simp only [List.mem_cons, List.not_mem_nil, or_false,
      Bool.false_eq_true, Bool.true_eq_false, or_true, true_or]
  · change (p.catalog,p.context,p.entry,p.initialWider,p.steps) ∈
      lowerHistoryWalkKeys p.catalog p.context p.entry p.initialWider
        (lowerHistoryInitialState p) [] 7
    simpa only [List.nil_append] using
      au_walk_complete p.catalog p.context p.entry p.initialWider
        (lowerHistoryInitialState p) [] p.steps 7 hp.1 hp.2.2.1
        (au_structural_terminal p hp)

#print axioms solution
