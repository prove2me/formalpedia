-- Prove2me | solution 1 for FairSelling.GeneralTPS.pool_emptyStage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:16.040552+00:00
-- url     : https://prove2.me/submissions/836bdfd6-1310-438e-a25b-7d7c5b838ff6

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.GeneralTPS
theorem _root_.solution : (emptyStage G n).pool = Finset.univ := by
  ext x
  simp [Stage.pool, emptyStage]
end FairSelling.GeneralTPS
