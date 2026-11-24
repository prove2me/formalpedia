-- Prove2me | solution 1 for FairSelling.MMSEP_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:54:55.159867+00:00
-- url     : https://prove2.me/submissions/13204505-f631-4b86-b9e0-f4e1fbc20b6f

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
import Theorems.Thm_FairSelling_mem_MMSEPset_zero
import Theorems.Thm_FairSelling_le_MMSEP

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    0 ≤ MMSEP n v p :=
  le_MMSEP v p hn hv hp (mem_MMSEPset_zero v p)
end FairSelling
