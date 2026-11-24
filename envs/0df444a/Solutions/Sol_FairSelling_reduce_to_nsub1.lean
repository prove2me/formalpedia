-- Prove2me | solution 1 for FairSelling.reduce_to_nsub1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:04.651397+00:00
-- url     : https://prove2.me/submissions/6f043c67-ad60-4b45-b33c-f511fecf5a5d

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Theorems.Thm_FairSelling_reduce_stepN

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (n : ℕ) (hn : 0 < n) (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (r : ℝ) :
    ∀ (k : ℕ) (A : Fin n → Finset G) (s : Finset G) (q : Fin n → ℝ),
      ConfigN n w p r A s q → s.card ≤ k →
      ∃ (A' : Fin n → Finset G) (s' : Finset G) (q' : Fin n → ℝ),
        ConfigN n w p r A' s' q' ∧ s'.card ≤ n - 1 := by
  intro k;
  induction' k with k ih;
  · exact fun A s q h1 h2 => ⟨ A, s, q, h1, by omega ⟩;
  · intro A s q hcfg hcard;
    by_cases hcase : s.card ≤ n - 1;
    · exact ⟨ A, s, q, hcfg, hcase ⟩;
    · obtain ⟨ A', s', q', hcfg', hcard' ⟩ := reduce_stepN n hn w p hp r A s q hcfg ( by omega );
      exact ih A' s' q' hcfg' ( by omega )
end FairSelling
