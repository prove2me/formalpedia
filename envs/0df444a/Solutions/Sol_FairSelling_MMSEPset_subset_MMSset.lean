-- Prove2me | solution 1 for FairSelling.MMSEPset_subset_MMSset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:48:27.906308+00:00
-- url     : https://prove2.me/submissions/73ecc840-5af5-4a93-97da-61ad41706f2f

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) : MMSEPset n v p ⊆ MMSset n v p := by
  rintro r ⟨o, hvalid, -, hguar⟩
  exact ⟨o, hvalid, hguar⟩
end FairSelling
