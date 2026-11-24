-- Prove2me | solution 1 for FairChores.LitCounterexample.oo_not_SEFXlit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:22:22.128555+00:00
-- url     : https://prove2.me/submissions/e1274e8a-7282-48e8-ab47-45f164be382d

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
import Theorems.Thm_FairChores_LitCounterexample_cbarSum_kept
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
open FairChores.LitCounterexample
namespace FairChores.LitCounterexample
theorem _root_.solution : ¬ SEFXlit cc pp oo := by
  intro h
  have h2 := (h 0 1).2 (by simp [oo]) 0 (by simp [oo])
  rw [cbarSum_kept, cbarSum_kept] at h2
  norm_num [oo, cc, pp] at h2
end FairChores.LitCounterexample
