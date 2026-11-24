-- Prove2me | solution 1 for FairSelling.PotTPS.slice_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:00:51.602908+00:00
-- url     : https://prove2.me/submissions/bc6360f0-facd-4258-84db-4681cbebbeeb

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling.PotTPS
theorem _root_.solution (w p : G → ℝ) (t τ : ℝ) (g : G) (a c : ℝ)
    (hac : a + c ≤ p g) (hat : a ≤ τ) (ht : t ≤ 2 * τ) :
    a + (saleLoss w p t g + min c τ) ≤ 2 * τ := by
  have hmin1 : min c τ ≤ c := min_le_left _ _
  have hmin2 : min c τ ≤ τ := min_le_right _ _
  unfold saleLoss trunc
  rcases max_cases (p g) (min (w g) t) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he]
  · linarith
  · have h1 : min (w g) t ≤ t := min_le_right _ _
    linarith
end FairSelling.PotTPS
