-- Prove2me | solution 1 for FairSelling.MMSset_le_PS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:31:11.431954+00:00
-- url     : https://prove2.me/submissions/82147de2-169e-438d-985f-bc8864bc81c6

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
import Theorems.Thm_FairSelling_PS_nonneg
import Theorems.Thm_FairSelling_TPSset_le_PS
import Theorems.Thm_FairSelling_mem_TPSset_of_valid


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g)
    {r : ℝ} (hr : r ∈ MMSset n v p) : r ≤ PS n v p := by
  rcases le_or_gt 0 r with hr0 | hr0
  · obtain ⟨o, hvalid, hguar⟩ := hr
    exact TPSset_le_PS v p (mem_TPSset_of_valid v p hn hv hp o hvalid r hr0 hguar)
  · exact le_trans hr0.le (PS_nonneg v p hp)
end FairSelling
