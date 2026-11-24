-- Prove2me | solution 1 for FairSelling.theorem_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:46:26.239807+00:00
-- url     : https://prove2.me/submissions/296e6ad1-03c0-4239-b732-ed837a9d8f09

import Mathlib
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxPotImp
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSSefxTheorem2
import Theorems.Thm_FairSelling_theorem_two_SEFX
import Theorems.Thm_FairSelling_exists_TPS_approx


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) :
    (∃ o : Outcome G n, o.Valid p ∧
      ∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧
    (∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o) :=
  ⟨exists_TPS_approx v p hn hp, theorem_two_SEFX v p hn hp⟩
end FairSelling
