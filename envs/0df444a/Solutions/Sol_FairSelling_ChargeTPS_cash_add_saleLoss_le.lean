-- Prove2me | solution 1 for FairSelling.ChargeTPS.cash_add_saleLoss_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:40.729091+00:00
-- url     : https://prove2.me/submissions/b872ca37-2aaf-46ee-b658-5b0592f60cf9

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxCharge

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling.ChargeTPS
theorem _root_.solution (w p : G → ℝ) (t : ℝ) (g : G) (c : ℝ) (hc : c ≤ p g) (hct : c ≤ t) :
    c + saleLoss w p t g ≤ t := by
  unfold saleLoss trunc
  rcases max_cases (p g) (min (w g) t) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he]
  · linarith
  · have : min (w g) t ≤ t := min_le_right _ _
    linarith
end FairSelling.ChargeTPS
