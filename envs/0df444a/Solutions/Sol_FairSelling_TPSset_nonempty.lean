-- Prove2me | solution 1 for FairSelling.TPSset_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:36:33.486836+00:00
-- url     : https://prove2.me/submissions/17ab8286-9e6e-4b02-9568-a0db69fb4825

import Mathlib
import Definitions.Def_RequestProject_Selling
import Theorems.Thm_FairSelling_mem_TPSset_zero

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) :
    (TPSset n v p).Nonempty := ⟨0, mem_TPSset_zero v p hp⟩
end FairSelling
