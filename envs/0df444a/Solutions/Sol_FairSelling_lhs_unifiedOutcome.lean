-- Prove2me | solution 1 for FairSelling.lhs_unifiedOutcome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:29.350049+00:00
-- url     : https://prove2.me/submissions/9837a543-73db-4f45-96f5-ec091e2d438e

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSSefx
import Theorems.Thm_FairSelling_vbarSum_kept_unifiedOutcome
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_util_unifiedOutcome
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ)
    (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ) (i : Fin n) :
    vbarSum (v i) p ((unifiedOutcome v p A F q).kept i) + (unifiedOutcome v p A F q).money i
      = vbarSum (v i) p (A i) + q i := by
  rw [vbarSum_kept_unifiedOutcome]
  have := util_unifiedOutcome v p A F q i
  simpa [util] using this
end FairSelling
