-- Prove2me | solution 1 for FairSelling.MMSset_bddAbove_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:53.603946+00:00
-- url     : https://prove2.me/submissions/1046eda5-a759-4b0d-9a74-722707c6c793

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
import Theorems.Thm_FairSelling_exists_max_outcome
import Theorems.Thm_FairSelling_mem_MMSset_iff


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    BddAbove (MMSset n v p) := by
  obtain ⟨o, hovalid, _hcover, homax⟩ := exists_max_outcome v p hv hp hn
  refine ⟨minUtil v o, fun r hr => ?_⟩
  obtain ⟨o', hv', hr'⟩ := (mem_MMSset_iff hn v p r).mp hr
  exact hr'.trans (homax o' hv')
end FairSelling
