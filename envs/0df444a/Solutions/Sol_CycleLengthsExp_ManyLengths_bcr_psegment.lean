-- Prove2me | solution 1 for CycleLengthsExp.ManyLengths.bcr_psegment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:30:48.592696+00:00
-- url     : https://prove2.me/submissions/02fad56d-fdb5-4f8a-92d2-2aeb82a4d6d1

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

open CycleLengthsExp.ManyLengths
/-- P-segment glue (Friedman–Krivelevich, p. 14, proof of Theorem 2).

Setup: `P` is a path in `G` from `u` to `v`.

Conclusion: there is a segment function `seg` assigning to every pair
`a, b ∈ P.support` a walk `seg a b` in `G` from `a` to `b`, such that:
(i) every segment is a path; (ii) every segment's support is contained in
`P.support`; (iii) the segment's length is the index distance
`|idxOf b - idxOf a|` along `P` (via the `if` on the order of the two
indices); and (iv) `idxOf` is injective on `P.support`.

Proof sketch: for `a, b ∈ P.support`, if `pos a ≤ pos b` the segment is
`(P.dropUntil a).takeUntil b`, else the reverse direction. The length
formula follows from `take_spec` (`takeUntil ++ dropUntil = whole`) +
support prefix/suffix lemmas (`support_takeUntil_prefix_support`,
`support_dropUntil_suffix_support`): for a path, support is nodup, so
`P.support.idxOf a = (P.takeUntil a).length`, and the segment's support is
the sublist from `a` to `b`, giving `length = |idxOf b - idxOf a|`. InjOn
`idxOf` on `P.support` is `List.idxOf_inj` + nodup.

This is DEEP INPUT B of the decomposition of
`CycleLengthsExp.ManyLengths.branch_cycles_repaired` (parent, Open): the
assembly consumes `seg` and the length formula to build one cycle per
`w ∈ X₃` as (P-segment `w₀ → w`) ++ (T-leg `w → w₀`), with the length
formula giving the cycle length `A + segLen w` and `idxOf` injectivity
giving `InjOn segLen X₃`. -/
theorem cl_prefix_mem {α : Type*} [DecidableEq α] {l₁ l₂ : List α} (hp : l₁ <+: l₂) {a : α}
    (ha : a ∈ l₂) (hlt : l₂.idxOf a < l₁.length) : a ∈ l₁ ∧ l₁.idxOf a = l₂.idxOf a := by
  obtain ⟨t, rfl⟩ := hp
  by_cases h : a ∈ l₁
  · exact ⟨h, (List.idxOf_append_of_mem h).symm⟩
  · rw [List.idxOf_append_of_notMem h] at hlt; omega

theorem cl_seg {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} (P : G.Walk u v) (hP : P.IsPath)
    (a b : Fin n) (ha : a ∈ P.support) (hb : b ∈ P.support)
    (hab : P.support.idxOf a ≤ P.support.idxOf b) :
    ∃ W : G.Walk a b, W.IsPath ∧ W.support ⊆ P.support ∧
      W.length = P.support.idxOf b - P.support.idxOf a := by
  have hpre := P.support_takeUntil_prefix_support hb
  have hlen : (P.takeUntil b hb).support.length = P.support.idxOf b + 1 := by
    rw [SimpleGraph.Walk.length_support, SimpleGraph.Walk.length_takeUntil]
  obtain ⟨ha', hidx⟩ := cl_prefix_mem hpre ha (by omega)
  refine ⟨(P.takeUntil b hb).dropUntil a ha', (hP.takeUntil hb).dropUntil ha', ?_, ?_⟩
  · intro x hx
    exact P.support_takeUntil_subset hb ((P.takeUntil b hb).support_dropUntil_subset ha' hx)
  · rw [SimpleGraph.Walk.length_dropUntil, SimpleGraph.Walk.length_takeUntil, hidx]

theorem solution (n : ℕ) (G : SimpleGraph (Fin n))
    (u v : Fin n) (P : G.Walk u v) (hPpath : P.IsPath) :
    ∃ (seg : ∀ (a b : Fin n), a ∈ P.support → b ∈ P.support → G.Walk a b),
      (∀ a b ha hb, (seg a b ha hb).IsPath) ∧
      (∀ a b ha hb, (seg a b ha hb).support ⊆ P.support) ∧
      (∀ a b ha hb, (seg a b ha hb).length =
        if P.support.idxOf a ≤ P.support.idxOf b then
          P.support.idxOf b - P.support.idxOf a else
          P.support.idxOf a - P.support.idxOf b) ∧
      (∀ a ∈ P.support, ∀ b ∈ P.support,
        P.support.idxOf a = P.support.idxOf b → a = b) := by
  classical
  have key : ∀ a b, a ∈ P.support → b ∈ P.support → ∃ W : G.Walk a b, W.IsPath ∧ W.support ⊆ P.support ∧
      W.length = (if P.support.idxOf a ≤ P.support.idxOf b then
          P.support.idxOf b - P.support.idxOf a else
          P.support.idxOf a - P.support.idxOf b) := by
    intro a b ha hb
    by_cases h : P.support.idxOf a ≤ P.support.idxOf b
    · obtain ⟨W, h1, h2, h3⟩ := cl_seg P hPpath a b ha hb h
      exact ⟨W, h1, h2, by rw [if_pos h, h3]⟩
    · obtain ⟨W, h1, h2, h3⟩ := cl_seg P hPpath b a hb ha (by omega)
      refine ⟨W.reverse, h1.reverse, by rw [SimpleGraph.Walk.support_reverse]; intro x hx; exact h2 (List.mem_reverse.mp hx), ?_⟩
      rw [if_neg h, SimpleGraph.Walk.length_reverse, h3]
  choose seg hseg using key
  refine ⟨seg, fun a b ha hb => (hseg a b ha hb).1, fun a b ha hb => (hseg a b ha hb).2.1,
    fun a b ha hb => (hseg a b ha hb).2.2, ?_⟩
  intro a ha b _ h
  exact (List.idxOf_inj ha).mp h


