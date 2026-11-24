-- Prove2me | solution 1 for FairSelling.ChargeTPS.cost_eq_zero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:46.960632+00:00
-- url     : https://prove2.me/submissions/5826750a-b9e2-4c5c-a7ee-43a115dcd71b

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxCharge
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open CStage
namespace FairSelling.ChargeTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) {s : CStage G n}
    (hs : s.Good v p eps) {i : Fin n} (hi : i ∉ s.served) (j : Fin n) : s.cost v p i j = 0 := by
  obtain ⟨hb, hc, hcash, hresv⟩ := hs.1 i hi
  simp [CStage.cost, hb, hc, hcash, hresv, truncBundle]
end FairSelling.ChargeTPS
