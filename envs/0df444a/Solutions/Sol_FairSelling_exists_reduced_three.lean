-- Prove2me | solution 1 for FairSelling.exists_reduced_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:34.549351+00:00
-- url     : https://prove2.me/submissions/85f9efdc-17b6-48ec-bb7b-7c44bb7d2e46

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Theorems.Thm_FairSelling_exists_reducedN

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g) :
    ∃ (A : Fin 3 → Finset G) (s : Finset G) (q : Fin 3 → ℝ),
      ConfigN 3 w p (MMS 3 w p) A s q ∧ s.card ≤ 2 := by
  obtain ⟨A, s, q, hcfg, hcard⟩ := exists_reducedN 3 (by norm_num) w p hw hp
  exact ⟨A, s, q, hcfg, by simpa using hcard⟩
end FairSelling
