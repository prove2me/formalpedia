-- Prove2me | solution 1 for FairSelling.le_MMS_of_outcome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:32:47.572321+00:00
-- url     : https://prove2.me/submissions/a71b152d-cda8-4c72-9260-ca8c258e43de

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
import Theorems.Thm_FairSelling_MMSset_bddAbove_of

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g)
    (o : Outcome G n) (ho : o.Valid p) (r : ℝ) (hr : ∀ j, r ≤ util v o j) :
    r ≤ MMS n v p :=
  le_csSup (MMSset_bddAbove_of hn v p hv hp) ⟨o, ho, hr⟩
end FairSelling
