-- Prove2me | solution 1 for FairSelling.vbar_le_of_mem_part
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:12:04.636247+00:00
-- url     : https://prove2.me/submissions/f5d53e77-8696-4807-bf8a-eb3b41991574

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsBudget
import Theorems.Thm_FairSelling_Canonical_cash_nonneg
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable {w p : G → ℝ} {μ : ℝ} {k : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g)
    {j : Fin k} {g : G} (hg : g ∈ E.part j) : vbar w p g ≤ μ := by
  classical
  have h1 : vbar w p g ≤ vbarSum w p (E.part j) := by
    refine Finset.single_le_sum (f := fun x => vbar w p x) (fun x _ => ?_) hg
    exact le_trans (hp x) (le_max_left _ _)
  have h2 := E.value j
  have h3 := E.cash_nonneg j
  simp only [vbarSum] at h1 h2
  linarith
end FairSelling
