-- Prove2me | solution 1 for D1Bound5.pellCFAt_mem_trace
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:10:41.606308+00:00
-- url     : https://prove2.me/submissions/6ade5609-cc54-4b5b-af9b-a7ce81184594

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions

section
namespace D1Bound5



























theorem _root_.solution (d a0 : ℤ) (s : PellCFState) {n N : ℕ} (hn : n ≤ N) :
    pellCFAt d a0 s n ∈ pellCFTrace d a0 s N := by
  induction N generalizing s n with
  | zero =>
      have hn0 : n = 0 := by omega
      simp [hn0,pellCFAt,pellCFTrace]
  | succ N ih =>
      cases n with
      | zero => simp [pellCFAt,pellCFTrace]
      | succ n =>
          exact List.mem_cons_of_mem _ (ih (pellCFStep d a0 s) (by omega))























end D1Bound5
end
