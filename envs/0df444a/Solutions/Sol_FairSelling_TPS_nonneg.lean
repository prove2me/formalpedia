-- Prove2me | solution 1 for FairSelling.TPS_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:33.657802+00:00
-- url     : https://prove2.me/submissions/18f6a93c-471b-4846-9955-f09f65bfa1b8

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Theorems.Thm_FairSelling_TPSset_bddAbove
import Theorems.Thm_FairSelling_mem_TPSset_zero


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) : 0 ≤ TPS n v p :=
  le_csSup (TPSset_bddAbove v p) (mem_TPSset_zero v p hp)
end FairSelling
