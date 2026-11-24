-- Prove2me | solution 1 for FairChores.reduce_to_oneC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:01:05.108721+00:00
-- url     : https://prove2.me/submissions/ecd8e8ac-fb8c-46db-b6f3-7d88f0a39b19

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
import Theorems.Thm_FairChores_reduce_stepC

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (c p : T → ℝ) (hp : ∀ t, 0 ≤ p t) (r : ℝ) :
    ∀ (k : ℕ) (A : Fin 2 → Finset T) (s : Finset T) (q : Fin 2 → ℝ),
      ConfigC c p r A s q → s.card ≤ k →
      ∃ (A' : Fin 2 → Finset T) (s' : Finset T) (q' : Fin 2 → ℝ),
        ConfigC c p r A' s' q' ∧ s'.card ≤ 1 := by
  intro k
  induction k with
  | zero =>
    intro A s q hcfg hk
    exact ⟨A, s, q, hcfg, hk.trans (by norm_num)⟩
  | succ k ih =>
    intro A s q hcfg hk
    by_cases hc : s.card ≤ 1
    · exact ⟨A, s, q, hcfg, hc⟩
    · have h2 : 2 ≤ s.card := by omega
      obtain ⟨A', s', q', hcfg', hlt⟩ := reduce_stepC c p hp r A s q hcfg h2
      exact ih A' s' q' hcfg' (by omega)
end FairChores
