-- Prove2me | solution 1 for FairSelling.MMS_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:00.051752+00:00
-- url     : https://prove2.me/submissions/a58626cb-35b7-4b37-8b65-6aa5495d2c07

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Theorems.Thm_FairSelling_mem_MMSset_iff
import Theorems.Thm_FairSelling_exists_max_outcome

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
namespace FairSelling
theorem _root_.solution (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    MMS n v p ∈ MMSset n v p := by
  obtain ⟨o, hovalid, _hcover, homax⟩ := exists_max_outcome v p hv hp hn
  have hub : ∀ r ∈ MMSset n v p, r ≤ minUtil v o := by
    intro r hr
    obtain ⟨o', hv', hr'⟩ := (mem_MMSset_iff hn v p r).mp hr
    exact hr'.trans (homax o' hv')
  have hmem : minUtil v o ∈ MMSset n v p := (mem_MMSset_iff hn v p _).mpr ⟨o, hovalid, le_refl _⟩
  have hbdd : BddAbove (MMSset n v p) := ⟨minUtil v o, fun r hr => hub r hr⟩
  have hEq : MMS n v p = minUtil v o := le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup hbdd hmem)
  show MMS n v p ∈ MMSset n v p
  rw [hEq]; exact hmem
end FairSelling
