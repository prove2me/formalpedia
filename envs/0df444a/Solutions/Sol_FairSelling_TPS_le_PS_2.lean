-- Prove2me | solution 2 for FairSelling.TPS_le_PS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:56.16887+00:00
-- url     : https://prove2.me/submissions/4b6fb959-7d97-48b6-939d-6ba2d5abd335

import Mathlib
import Definitions.Def_RequestProject_Selling
import Theorems.Thm_FairSelling_mem_TPSset_zero
import Theorems.Thm_FairSelling_TPSset_le_PS

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) :
    TPS n v p ≤ PS n v p := by
  refine' csSup_le ( _ ) _;
  · exact ⟨ 0, mem_TPSset_zero v p hp ⟩;
  · intro t ht
    apply TPSset_le_PS v p ht
end FairSelling
