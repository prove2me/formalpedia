-- Prove2me | solution 1 for FairSelling.MMS_le_TPS_le_PS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:21.841834+00:00
-- url     : https://prove2.me/submissions/a3f4fd29-0a21-4f93-9f31-4556afd9c5e0

import Mathlib
import Definitions.Def_RequestProject_Selling
import Theorems.Thm_FairSelling_MMS_le_TPS
import Theorems.Thm_FairSelling_TPS_le_PS

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hn : 0 < n)
    (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    MMS n v p ≤ TPS n v p ∧ TPS n v p ≤ PS n v p :=
  ⟨MMS_le_TPS v p hn hv hp, TPS_le_PS v p hp⟩
end FairSelling
