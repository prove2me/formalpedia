-- Prove2me | solution 1 for FairChores.cbarSum_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:19:16.309278+00:00
-- url     : https://prove2.me/submissions/b0f6b95c-8ec3-4d85-9a07-7223f9ab05a5

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
omit [Fintype T]
namespace FairChores
theorem _root_.solution (c p : T → ℝ) {A B : Finset T} (h : A ⊆ B) :
    cbarSum c p B = cbarSum c p (B \ A) + cbarSum c p A := by
  simp only [cbarSum]
  rw [← Finset.sum_sdiff h]
end FairChores
