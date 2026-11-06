-- Prove2me | solution 2 for ENP.infinitely_often
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:32:12.749217+00:00
-- url     : https://prove2.me/submissions/4bc7e94e-8fac-4bd6-98d1-0d129eb1ad4b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf
import Theorems.Thm_ENP_allDecided
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
namespace ENP
theorem _root_.solution {L : ENP.Lang} (h : ¬ENP.HasLinearCircuits L) (c N : ℕ) : ∃ n, N ≤ n ∧ ¬ENP.DecidedAt L (c * (n + 1)) n := by
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
    have h1 : s n ≤ ∑ n ∈ Finset.range N, s n := Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
    calc s n ≤ (c + ∑ n ∈ Finset.range N, s n) * 1 := by omega
      _ ≤ (c + ∑ n ∈ Finset.range N, s n) * (n + 1) := Nat.mul_le_mul_left _ (by omega)
end ENP
