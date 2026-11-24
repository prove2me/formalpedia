-- Prove2me | solution 1 for FairSelling.exists_outcome_ge_MMS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:36:41.822605+00:00
-- url     : https://prove2.me/submissions/60629eed-cb0c-48ea-9dd6-b1c1ff684982

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Theorems.Thm_FairSelling_MMS_mem

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
namespace FairSelling
theorem _root_.solution (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧ ∀ j, MMS n v p ≤ util v o j :=
  MMS_mem hn v p hv hp
end FairSelling
