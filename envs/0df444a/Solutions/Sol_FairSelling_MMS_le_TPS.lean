-- Prove2me | solution 1 for FairSelling.MMS_le_TPS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:50.53658+00:00
-- url     : https://prove2.me/submissions/a6648906-3c89-4880-b2f8-eb2eb1dde5d3

import Mathlib
import Definitions.Def_RequestProject_Selling
import Theorems.Thm_FairSelling_MMSset_nonempty
import Theorems.Thm_FairSelling_mem_TPSset_zero
import Theorems.Thm_FairSelling_TPSset_bddAbove
import Theorems.Thm_FairSelling_mem_TPSset_of_valid

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hn : 0 < n)
    (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    MMS n v p ≤ TPS n v p := by
  by_contra h_contra;
  obtain ⟨r, hr⟩ : ∃ r, r ∈ MMSset n v p ∧ r > TPS n v p := by
    exact exists_lt_of_lt_csSup ( MMSset_nonempty v p ) ( not_le.mp h_contra );
  obtain ⟨o, hvalid, hguar⟩ := hr.left
  have hr_nonneg : 0 ≤ r := by
    exact le_trans ( by exact le_csSup ( TPSset_bddAbove v p ) ( mem_TPSset_zero v p hp ) ) hr.right.le
  have hr_in_TPSset : r ∈ TPSset n v p := by
    exact mem_TPSset_of_valid v p hn hv hp o hvalid r hr_nonneg hguar
  have hr_le_TPS : r ≤ TPS n v p := by
    exact le_csSup ( TPSset_bddAbove v p ) hr_in_TPSset
  linarith [hr.right]
end FairSelling
