-- Prove2me | solution 2 for FairSelling.TPSset_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:54.289594+00:00
-- url     : https://prove2.me/submissions/299a5671-c35d-4d14-a8fb-6ff2658f9d96

import Mathlib
import Definitions.Def_RequestProject_Selling
import Theorems.Thm_FairSelling_TPSset_le_PS

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) :
    BddAbove (TPSset n v p) := ⟨PS n v p, fun _ ht => TPSset_le_PS v p ht⟩
end FairSelling
