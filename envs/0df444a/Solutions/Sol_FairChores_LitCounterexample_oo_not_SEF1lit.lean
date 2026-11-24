-- Prove2me | solution 1 for FairChores.LitCounterexample.oo_not_SEF1lit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:22:31.827993+00:00
-- url     : https://prove2.me/submissions/02881658-a136-46cb-b420-7a7cc00f5479

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
theorem _root_.solution : ¬ SEF1lit cc pp oo := by
  intro h
  obtain ⟨t, ht, h2⟩ := (h 0 1).2 (by simp [oo])
  rw [cbarSum_kept, cbarSum_kept] at h2
  norm_num [oo, cc, pp] at h2
end FairChores.LitCounterexample
