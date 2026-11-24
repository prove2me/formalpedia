-- Prove2me | solution 1 for FairSelling.le_MMSEP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:34:44.877764+00:00
-- url     : https://prove2.me/submissions/0fe5baf3-694f-4a00-ae03-08033b1e5ca6

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
import Theorems.Thm_FairSelling_MMSEPset_bddAbove

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g)
    {r : ℝ} (hr : r ∈ MMSEPset n v p) : r ≤ MMSEP n v p :=
  le_csSup (MMSEPset_bddAbove v p hn hv hp) hr
end FairSelling
