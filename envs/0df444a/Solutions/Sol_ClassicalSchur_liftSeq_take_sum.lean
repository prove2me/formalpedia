-- Prove2me | solution 1 for ClassicalSchur.liftSeq_take_sum
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-26T21:35:52.74244+00:00
-- url     : https://prove2.me/submissions/3083d063-e009-4c5c-b069-1144f28dd577

-- Generated from lean/ClassicalSchur/Lift.lean
--   imports : 1 platform node(s), 1 definition bundle(s)
--   inlined : 0 file-scoped / sub-threshold helper(s)
--   rename  : liftSeq_take_sum -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurLift
import Theorems.Thm_ClassicalSchur_liftPrefix_strictMono
import Mathlib



open ClassicalSchur in
theorem solution {m₁ m₂ M : ℕ} (hm₁ : 0 < m₁) (hM : m₁ ≤ M) {L : ℕ}
    (hL : L ≤ m₁ * m₂ - 1) : ((liftSeq m₁ m₂ M).take L).sum = liftPrefix m₁ M L := by
  have hmono := (liftPrefix_strictMono hm₁ hM).monotone
  have key : ∀ n, ((List.range n).map
      fun k => liftPrefix m₁ M (k + 1) - liftPrefix m₁ M k).sum = liftPrefix m₁ M n := by
    intro n
    induction n with
    | zero => simp [liftPrefix]
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      have := hmono (show n ≤ n + 1 by omega)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
  rw [liftSeq, ← List.map_take, List.take_range, Nat.min_eq_left hL, key]
