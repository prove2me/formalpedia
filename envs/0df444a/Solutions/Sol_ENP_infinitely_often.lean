-- Prove2me | solution 1 for ENP.infinitely_often
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T08:48:56.824376+00:00
-- url     : https://prove2.me/submissions/8c8799bb-9001-4dab-8539-3614c0483433

import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf
import Theorems.Thm_ENP_allDecided

set_option autoImplicit false

open ENP

theorem solution {L : ENP.Lang} (h : ¬ENP.HasLinearCircuits L) (c N : ℕ) :
    ∃ n, N ≤ n ∧ ¬ENP.DecidedAt L (c * (n + 1)) n := by
  by_contra hc
  have hc : ∀ n, N ≤ n → ENP.DecidedAt L (c * (n + 1)) n := by
    intro n hn
    by_contra h'
    exact hc ⟨n, hn, h'⟩
  choose s hs using ENP.allDecided L
  refine h ⟨c + ∑ n ∈ Finset.range N, s n, fun n => ?_⟩
  by_cases hn : N ≤ n
  · obtain ⟨C, hC, hd⟩ := hc n hn
    exact ⟨C, hC.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)), hd⟩
  · obtain ⟨C, hC, hd⟩ := hs n
    refine ⟨C, hC.trans ?_, hd⟩
    have h1 : s n ≤ ∑ n ∈ Finset.range N, s n :=
      Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
    calc s n ≤ (c + ∑ n ∈ Finset.range N, s n) * 1 := by omega
      _ ≤ (c + ∑ n ∈ Finset.range N, s n) * (n + 1) := Nat.mul_le_mul_left _ (by omega)
