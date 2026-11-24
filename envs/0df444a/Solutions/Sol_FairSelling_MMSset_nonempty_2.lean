-- Prove2me | solution 2 for FairSelling.MMSset_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:51:48.389751+00:00
-- url     : https://prove2.me/submissions/32b9b075-c0e0-44e0-abf8-80790f5e267d

import Mathlib
import Definitions.Def_RequestProject_Selling
import Theorems.Thm_FairSelling_mem_MMSset_zero

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) :
    (MMSset n v p).Nonempty := ⟨0, mem_MMSset_zero v p⟩
end FairSelling
