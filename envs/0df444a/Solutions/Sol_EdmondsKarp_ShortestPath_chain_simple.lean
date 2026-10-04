-- Prove2me | solution 1 for EdmondsKarp.ShortestPath.chain_simple
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T19:35:56.007926+00:00
-- url     : https://prove2.me/submissions/5c363731-80bf-4764-8301-9b822f8aebfc

import Mathlib

theorem solution {V : Type} [DecidableEq V] (R : V → V → Prop) (P : List V)
    (hP : P.IsChain R) :
    ∃ Q : List V, Q.Nodup ∧ Q.IsChain R ∧ Q.head? = P.head? ∧
      Q.getLast? = P.getLast? ∧ Q.length ≤ P.length := by
  induction P with
  | nil => exact ⟨[], by simp⟩
  | cons a L ih =>
    obtain ⟨Q, hnd, hc, hh, hl, hlen⟩ := ih hP.tail
    by_cases ha : a ∈ Q
    · have hi : Q.idxOf a < Q.length := List.idxOf_lt_length_iff.mpr ha
      have hL : L ≠ [] := by
        intro he
        have : Q.length = 0 := by simpa [he] using hlen
        have hQ : Q = [] := by simpa using this
        simp [hQ] at ha
      refine ⟨Q.drop (Q.idxOf a), hnd.sublist (List.drop_sublist _ _), hc.drop _, ?_, ?_, ?_⟩
      · simpa using List.getElem?_idxOf ha
      · rw [List.getLast?_drop, if_neg (by omega), hl, List.getLast?_cons_of_ne_nil hL]
      · simp only [List.length_drop, List.length_cons]
        omega
    · refine ⟨a :: Q, List.nodup_cons.mpr ⟨ha, hnd⟩, ?_, rfl, ?_, ?_⟩
      · apply hc.cons
        intro y hy
        rw [hh] at hy
        exact hP.rel_head? hy
      · simp only [List.getLast?_cons, hl]
      · simpa using hlen
