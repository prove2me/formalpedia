-- Prove2me | solution 1 for FairSelling.TPS_eq_PS_of_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:53:06.298288+00:00
-- url     : https://prove2.me/submissions/b904888a-08c3-402c-addc-58a375f396dd

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Theorems.Thm_FairSelling_le_TPS_of_le_truncSum
import Theorems.Thm_FairSelling_truncSum_of_ge
import Theorems.Thm_FairSelling_TPS_le_PS


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {s : ℝ}
    (hs : ∀ g, v g ≤ s) (hfs : s ≤ truncSum n v p s) :
    TPS n v p = PS n v p := by
  have hsPS : s ≤ PS n v p := by rw [← truncSum_of_ge v p hs]; exact hfs
  have hfix : PS n v p ≤ truncSum n v p (PS n v p) :=
    le_of_eq (truncSum_of_ge v p (fun g => le_trans (hs g) hsPS)).symm
  exact le_antisymm (TPS_le_PS v p hp) (le_TPS_of_le_truncSum v p hfix)
end FairSelling
