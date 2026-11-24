-- Prove2me | solution 1 for FairSelling.MMSset_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:32:23.892707+00:00
-- url     : https://prove2.me/submissions/24f4ccf1-633e-4055-9acb-64ac8f14be17

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
import Theorems.Thm_FairSelling_MMSset_le_PS

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    BddAbove (MMSset n v p) :=
  ⟨PS n v p, fun _ hr => MMSset_le_PS v p hn hv hp hr⟩
end FairSelling
