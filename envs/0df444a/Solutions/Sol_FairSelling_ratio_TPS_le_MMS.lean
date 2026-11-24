-- Prove2me | solution 1 for FairSelling.ratio_TPS_le_MMS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:41:09.45579+00:00
-- url     : https://prove2.me/submissions/e85e443c-df90-445a-9cd5-a027f689dbb0

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSSefx
import Theorems.Thm_FairSelling_exists_TPS_approx
import Theorems.Thm_FairSelling_le_MMS_of_outcome


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    ((n : ℝ) / (2 * n - 1)) * TPS n v p ≤ MMS n v p := by
  classical
  obtain ⟨o, hvalid, hserve⟩ := exists_TPS_approx (fun _ : Fin n => v) p hn hp
  exact le_MMS_of_outcome hn v p hv hp o hvalid _ (fun j => hserve j)
end FairSelling
