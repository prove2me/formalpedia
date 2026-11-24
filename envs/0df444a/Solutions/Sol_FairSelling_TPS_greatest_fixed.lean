-- Prove2me | solution 1 for FairSelling.TPS_greatest_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:36:41.169813+00:00
-- url     : https://prove2.me/submissions/08d3b19f-0887-41bc-971c-f17fb209e3f6

import Mathlib
import Definitions.Def_RequestProject_Selling
import Theorems.Thm_FairSelling_TPSset_bddAbove

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) {t : ℝ}
    (ht : truncSum n v p t = t) : t ≤ TPS n v p := by
  apply le_csSup;
  · convert TPSset_bddAbove v p using 1;
  · exact ht.ge
end FairSelling
