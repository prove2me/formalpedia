-- Prove2me | solution 1 for FairChores.cbarSum_sdiff_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:21:53.760247+00:00
-- url     : https://prove2.me/submissions/ae546865-4076-4b33-8c61-a72fec6e8fc4

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {ci p : T → ℝ}
omit [Fintype T]
namespace FairChores
theorem _root_.solution {A : Finset T} {t : T} (ht : t ∈ A) :
    cbarSum ci p A = cbarSum ci p (A \ {t}) + cbar ci p t := by
  classical
  have hA : A = insert t (A \ {t}) := by
    ext x
    by_cases hx : x = t <;> simp [hx, ht]
  rw [cbarSum, cbarSum, hA, Finset.sum_insert (by simp)]
  simp [add_comm]
end FairChores
