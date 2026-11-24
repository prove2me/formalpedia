-- Prove2me | solution 1 for FairSelling.MMSEP_le_PS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:32:28.098295+00:00
-- url     : https://prove2.me/submissions/288073ef-10bd-433c-9061-74bca8e29b5d

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
import Theorems.Thm_FairSelling_MMSEPset_subset_MMSset
import Theorems.Thm_FairSelling_MMSset_le_PS
import Theorems.Thm_FairSelling_MMSEP_le

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    MMSEP n v p ≤ PS n v p :=
  MMSEP_le v p fun _ hr => MMSset_le_PS v p hn hv hp (MMSEPset_subset_MMSset v p hr)
end FairSelling
