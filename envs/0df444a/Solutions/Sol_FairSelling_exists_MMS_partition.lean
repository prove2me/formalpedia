-- Prove2me | solution 1 for FairSelling.exists_MMS_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:48.26236+00:00
-- url     : https://prove2.me/submissions/95e133a5-b0af-4f45-b955-730e2fd2072e

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Theorems.Thm_FairSelling_le_minUtil_iff
import Theorems.Thm_FairSelling_mem_MMSset_iff
import Theorems.Thm_FairSelling_exists_max_outcome

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
namespace FairSelling
theorem _root_.solution (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧
      (o.sold ∪ Finset.univ.biUnion o.kept = Finset.univ) ∧ ∀ j, MMS n v p ≤ util v o j := by
  obtain ⟨o, hovalid, hcover, homax⟩ := exists_max_outcome v p hv hp hn
  have hub : ∀ r ∈ MMSset n v p, r ≤ minUtil v o := by
    intro r hr
    obtain ⟨o', hv', hr'⟩ := (mem_MMSset_iff hn v p r).mp hr
    exact hr'.trans (homax o' hv')
  have hmem : minUtil v o ∈ MMSset n v p := (mem_MMSset_iff hn v p _).mpr ⟨o, hovalid, le_refl _⟩
  have hbdd : BddAbove (MMSset n v p) := ⟨minUtil v o, fun r hr => hub r hr⟩
  have hEq : MMS n v p = minUtil v o := le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup hbdd hmem)
  refine ⟨o, hovalid, hcover, fun j => ?_⟩
  rw [hEq]
  exact (le_minUtil_iff hn v o (minUtil v o)).mp (le_refl _) j
end FairSelling
