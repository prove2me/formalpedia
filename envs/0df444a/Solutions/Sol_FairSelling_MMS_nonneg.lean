-- Prove2me | solution 1 for FairSelling.MMS_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:32:44.596436+00:00
-- url     : https://prove2.me/submissions/a373ff04-44b6-436f-9ff7-4ea1ad01500c

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
import Theorems.Thm_FairSelling_MMSset_bddAbove_of
import Theorems.Thm_FairSelling_mem_MMSset_zero


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    0 ≤ MMS n v p :=
  le_csSup (MMSset_bddAbove_of hn v p hv hp) (mem_MMSset_zero v p)
end FairSelling
