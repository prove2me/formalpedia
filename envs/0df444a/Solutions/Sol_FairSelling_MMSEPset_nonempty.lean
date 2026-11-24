-- Prove2me | solution 1 for FairSelling.MMSEPset_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:24:08.292814+00:00
-- url     : https://prove2.me/submissions/cc01d25a-d25b-4767-a35f-34d9555d6c64

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
import Theorems.Thm_FairSelling_mem_MMSEPset_zero

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) : (MMSEPset n v p).Nonempty :=
  ⟨0, mem_MMSEPset_zero v p⟩
end FairSelling
