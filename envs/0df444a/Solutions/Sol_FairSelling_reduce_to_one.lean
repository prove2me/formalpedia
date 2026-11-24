-- Prove2me | solution 1 for FairSelling.reduce_to_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:18.820962+00:00
-- url     : https://prove2.me/submissions/67d8d32a-3694-4dfd-804d-e15cf5e7491f

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Theorems.Thm_FairSelling_reduce_step

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (r : ℝ) :
    ∀ (k : ℕ) (A : Fin 2 → Finset G) (s : Finset G) (q : Fin 2 → ℝ),
      Config w p r A s q → s.card ≤ k →
      ∃ (A' : Fin 2 → Finset G) (s' : Finset G) (q' : Fin 2 → ℝ),
        Config w p r A' s' q' ∧ s'.card ≤ 1 := by
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
      obtain ⟨A', s', q', hcfg', hlt⟩ := reduce_step w p hp r A s q hcfg h2
      exact ih A' s' q' hcfg' (by omega)
end FairSelling
