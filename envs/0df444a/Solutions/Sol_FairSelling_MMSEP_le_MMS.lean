-- Prove2me | solution 1 for FairSelling.MMSEP_le_MMS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:33:36.30657+00:00
-- url     : https://prove2.me/submissions/2417a66d-387c-43f5-9452-078933141454

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
import Theorems.Thm_FairSelling_MMSEPset_subset_MMSset
import Theorems.Thm_FairSelling_MMSEPset_nonempty
import Theorems.Thm_FairSelling_MMSset_bddAbove

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    MMSEP n v p ≤ MMS n v p :=
  csSup_le_csSup (MMSset_bddAbove v p hn hv hp) (MMSEPset_nonempty v p)
    (MMSEPset_subset_MMSset v p)
end FairSelling
