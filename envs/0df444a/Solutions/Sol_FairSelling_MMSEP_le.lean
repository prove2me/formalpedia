-- Prove2me | solution 1 for FairSelling.MMSEP_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:25:37.899825+00:00
-- url     : https://prove2.me/submissions/50f5d026-a115-4e19-93d1-e9ac001ccc8f

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
import Theorems.Thm_FairSelling_MMSEPset_nonempty

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) {c : ℝ} (h : ∀ r ∈ MMSEPset n v p, r ≤ c) :
    MMSEP n v p ≤ c :=
  csSup_le (MMSEPset_nonempty v p) h
end FairSelling
